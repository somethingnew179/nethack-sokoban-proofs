/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3220 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (1 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3221 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3222 (p : Pattern) (guard : d910 p = 1) : d295 p ≤ (1 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3221 p hg
    simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3223 (p : Pattern) (guard : d1132 p = 1) : d295 p ≤ (1 : Int) + d57 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3220 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3222 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3224 (p : Pattern) (guard : d1132 p = 1) : d296 p ≤ (1 : Int) + d1223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d296, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3219 p hg
    simpa only [d296, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d296, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d296, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3225 (p : Pattern) (guard : d1132 p = 1) : d297 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d297, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3215 p hg
    simpa only [d297, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d297, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3224 p hg
    simpa only [d297, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3226 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (1 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3227 (p : Pattern) (guard : d910 p = 1) : d298 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3226 p hg
    simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3228 (p : Pattern) (guard : d1132 p = 1) : d299 p ≤ (1 : Int) + d28 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3212 p hg
    simpa only [d1132, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3227 p hg
    simpa only [d1132, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3229 (p : Pattern) (guard : d1132 p = 1) : d300 p ≤ (1 : Int) + d28 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3215 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3228 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3230 (p : Pattern) (guard : d1132 p = 1) : d301 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d301, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3229 p hg
    simpa only [d301, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d301, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3224 p hg
    simpa only [d301, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3231 (p : Pattern) (guard : d1132 p = 1) : d302 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3225 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3230 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3232 (p : Pattern) (guard : d0 p = 1) : d303 p ≤ (1 : Int) + d89 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3233 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (1 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3234 (p : Pattern) (guard : d910 p = 1) : d304 p ≤ (1 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3233 p hg
    simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3235 (p : Pattern) (guard : d1132 p = 1) : d305 p ≤ (1 : Int) + d89 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3232 p hg
    simpa only [d1132, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d1132, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3236 (p : Pattern) (guard : d1132 p = 1) : d306 p ≤ (1 : Int) + d1225 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d306, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3215 p hg
    simpa only [d306, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d306, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3235 p hg
    simpa only [d306, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3237 (p : Pattern) (guard : d0 p = 1) : d307 p ≤ (1 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3238 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d99 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3239 (p : Pattern) (guard : d910 p = 1) : d307 p ≤ (1 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare370 p hg
    simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3240 (p : Pattern) (guard : d1132 p = 1) : d307 p ≤ (1 : Int) + d100 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3239 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3241 (p : Pattern) (guard : d1132 p = 1) : d308 p ≤ (1 : Int) + d1226 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d308, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3236 p hg
    simpa only [d308, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d308, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3240 p hg
    simpa only [d308, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3242 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (1 : Int) + d89 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3243 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3244 (p : Pattern) (guard : d910 p = 1) : d309 p ≤ (1 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d309, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d910, d309, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d309, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d910, d309, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3245 (p : Pattern) (guard : d1132 p = 1) : d310 p ≤ (1 : Int) + d89 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3242 p hg
    simpa only [d1132, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3244 p hg
    simpa only [d1132, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3246 (p : Pattern) (guard : d1132 p = 1) : d311 p ≤ (1 : Int) + d1225 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d311, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3228 p hg
    simpa only [d311, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d311, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3245 p hg
    simpa only [d311, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3247 (p : Pattern) (guard : d0 p = 1) : d312 p ≤ (1 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3248 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3249 (p : Pattern) (guard : d910 p = 1) : d312 p ≤ (1 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3248 p hg
    simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3250 (p : Pattern) (guard : d1132 p = 1) : d312 p ≤ (1 : Int) + d110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3247 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3249 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3251 (p : Pattern) (guard : d1132 p = 1) : d313 p ≤ (1 : Int) + d1227 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d313, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3240 p hg
    simpa only [d313, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d313, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3250 p hg
    simpa only [d313, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3252 (p : Pattern) (guard : d1132 p = 1) : d314 p ≤ (1 : Int) + d1228 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d314, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3246 p hg
    simpa only [d314, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d314, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3251 p hg
    simpa only [d314, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3253 (p : Pattern) (guard : d1132 p = 1) : d315 p ≤ (1 : Int) + d1229 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d315, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3241 p hg
    simpa only [d315, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d315, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d315, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3254 (p : Pattern) (guard : d1132 p = 1) : d316 p ≤ (1 : Int) + d1230 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d316, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3231 p hg
    simpa only [d316, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d316, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3253 p hg
    simpa only [d316, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3255 (p : Pattern) (guard : d0 p = 1) : d298 p ≤ (1 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3256 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3257 (p : Pattern) (guard : d910 p = 1) : d317 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d317, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d910, d317, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d317, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3256 p hg
    simpa only [d910, d317, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3258 (p : Pattern) (guard : d1132 p = 1) : d318 p ≤ (1 : Int) + d28 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3255 p hg
    simpa only [d1132, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3257 p hg
    simpa only [d1132, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3259 (p : Pattern) (guard : d1132 p = 1) : d319 p ≤ (1 : Int) + d28 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3228 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3258 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3260 (p : Pattern) (guard : d1132 p = 1) : d320 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d320, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3259 p hg
    simpa only [d320, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d320, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3224 p hg
    simpa only [d320, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3261 (p : Pattern) (guard : d1132 p = 1) : d321 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3230 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3260 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3262 (p : Pattern) (guard : d1132 p = 1) : d322 p ≤ (1 : Int) + d1231 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d322, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3258 p hg
    simpa only [d322, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d322, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d322, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3263 (p : Pattern) (guard : d1132 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare3264 (p : Pattern) (guard : d1132 p = 1) : d323 p ≤ (1 : Int) + d1232 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d323, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3250 p hg
    simpa only [d323, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d323, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3263 p hg
    simpa only [d323, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3265 (p : Pattern) (guard : d1132 p = 1) : d324 p ≤ (1 : Int) + d1233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d324, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3262 p hg
    simpa only [d324, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d324, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3264 p hg
    simpa only [d324, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3266 (p : Pattern) (guard : d1132 p = 1) : d325 p ≤ (1 : Int) + d1234 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d325, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d325, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d325, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3265 p hg
    simpa only [d325, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3267 (p : Pattern) (guard : d1132 p = 1) : d326 p ≤ (1 : Int) + d1235 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d326, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3261 p hg
    simpa only [d326, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d326, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3266 p hg
    simpa only [d326, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3268 (p : Pattern) (guard : d1132 p = 1) : d327 p ≤ (1 : Int) + d1236 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d327, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3254 p hg
    simpa only [d327, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d327, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3267 p hg
    simpa only [d327, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3269 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d984, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d984, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3270 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3271 (p : Pattern) (guard : d915 p = 1) : d16 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3270 p hg
    simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3272 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3273 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3271 p hg
    simpa only [d984, d293, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3272 p hg
    simpa only [d984, d293, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3274 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3275 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1113 p hg
    simpa only [d984, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3152 p hg
    simpa only [d984, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3276 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3277 (p : Pattern) (guard : d915 p = 1) : d15 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3276 p hg
    simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3278 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d49 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3279 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3277 p hg
    simpa only [d984, d294, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d984, d294, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3280 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3279 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3281 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1120 p hg
    simpa only [d984, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3156 p hg
    simpa only [d984, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3282 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3283 (p : Pattern) (guard : d915 p = 1) : d53 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3284 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3285 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3283 p hg
    simpa only [d984, d295, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3284 p hg
    simpa only [d984, d295, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3286 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3287 (p : Pattern) (guard : d984 p = 1) : d296 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3280 p hg
    simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3286 p hg
    simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3288 (p : Pattern) (guard : d984 p = 1) : d297 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3274 p hg
    simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3287 p hg
    simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3289 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3290 (p : Pattern) (guard : d915 p = 1) : d16 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3289 p hg
    simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3291 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d72 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3292 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3290 p hg
    simpa only [d984, d293, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3291 p hg
    simpa only [d984, d293, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3293 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3292 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3294 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3295 (p : Pattern) (guard : d984 p = 1) : d298 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3290 p hg
    simpa only [d984, d298, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3294 p hg
    simpa only [d984, d298, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3296 (p : Pattern) (guard : d984 p = 1) : d299 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d299, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d299, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d299, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3295 p hg
    simpa only [d299, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3297 (p : Pattern) (guard : d984 p = 1) : d300 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d300, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d300, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d300, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d300, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3298 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3299 (p : Pattern) (guard : d915 p = 1) : d15 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3298 p hg
    simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3300 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3301 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3299 p hg
    simpa only [d984, d294, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d984, d294, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3302 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3301 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3303 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3304 (p : Pattern) (guard : d915 p = 1) : d53 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3303 p hg
    simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3305 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3304 p hg
    simpa only [d984, d295, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d984, d295, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3306 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3305 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3307 (p : Pattern) (guard : d984 p = 1) : d296 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d296, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3302 p hg
    simpa only [d296, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d296, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3306 p hg
    simpa only [d296, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3308 (p : Pattern) (guard : d984 p = 1) : d301 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d301, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3297 p hg
    simpa only [d301, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d301, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3307 p hg
    simpa only [d301, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3309 (p : Pattern) (guard : d984 p = 1) : d302 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d302, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3288 p hg
    simpa only [d302, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d302, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3308 p hg
    simpa only [d302, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3310 (p : Pattern) (guard : d984 p = 1) : d303 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d984, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3170 p hg
    simpa only [d984, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3311 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d90 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3312 (p : Pattern) (guard : d915 p = 1) : d86 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3311 p hg
    simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3313 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3314 (p : Pattern) (guard : d984 p = 1) : d304 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d304, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3312 p hg
    simpa only [d984, d304, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d304, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3313 p hg
    simpa only [d984, d304, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3315 (p : Pattern) (guard : d984 p = 1) : d305 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3310 p hg
    simpa only [d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3314 p hg
    simpa only [d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3316 (p : Pattern) (guard : d984 p = 1) : d306 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3274 p hg
    simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3315 p hg
    simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3317 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d984, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2315 p hg
    simpa only [d984, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3318 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (0 : Int) + d71 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3319 (p : Pattern) (guard : d915 p = 1) : d98 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3318 p hg
    simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3320 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d72 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3321 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3319 p hg
    simpa only [d984, d307, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3320 p hg
    simpa only [d984, d307, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3322 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3317 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3321 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3323 (p : Pattern) (guard : d984 p = 1) : d308 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3316 p hg
    simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3322 p hg
    simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3324 (p : Pattern) (guard : d984 p = 1) : d304 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d984, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d984, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3325 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3326 (p : Pattern) (guard : d915 p = 1) : d86 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3325 p hg
    simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3327 (p : Pattern) (guard : d984 p = 1) : d309 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d309, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3326 p hg
    simpa only [d984, d309, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d309, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d984, d309, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3328 (p : Pattern) (guard : d984 p = 1) : d310 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d310, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3324 p hg
    simpa only [d310, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d310, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d310, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3329 (p : Pattern) (guard : d984 p = 1) : d311 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d311, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d311, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d311, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3328 p hg
    simpa only [d311, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3330 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3319 p hg
    simpa only [d984, d307, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d307, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3331 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3317 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3332 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1174 p hg
    simpa only [d984, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d984, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3333 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3334 (p : Pattern) (guard : d915 p = 1) : d97 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3333 p hg
    simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3335 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3334 p hg
    simpa only [d984, d312, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d312, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3336 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3332 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3335 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3337 (p : Pattern) (guard : d984 p = 1) : d313 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d313, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3331 p hg
    simpa only [d313, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d313, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d313, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3338 (p : Pattern) (guard : d984 p = 1) : d314 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d314, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3329 p hg
    simpa only [d314, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d314, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3337 p hg
    simpa only [d314, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3339 (p : Pattern) (guard : d984 p = 1) : d315 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d315, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3323 p hg
    simpa only [d315, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d315, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3338 p hg
    simpa only [d315, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3340 (p : Pattern) (guard : d984 p = 1) : d316 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d316, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3309 p hg
    simpa only [d316, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d316, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3339 p hg
    simpa only [d316, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3341 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3342 (p : Pattern) (guard : d984 p = 1) : d298 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3271 p hg
    simpa only [d984, d298, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3341 p hg
    simpa only [d984, d298, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3343 (p : Pattern) (guard : d984 p = 1) : d299 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3342 p hg
    simpa only [d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3344 (p : Pattern) (guard : d984 p = 1) : d300 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3274 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3343 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3345 (p : Pattern) (guard : d984 p = 1) : d301 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3344 p hg
    simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3287 p hg
    simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3346 (p : Pattern) (guard : d984 p = 1) : d298 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d984, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3194 p hg
    simpa only [d984, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3347 (p : Pattern) (guard : d984 p = 1) : d317 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d317, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3290 p hg
    simpa only [d984, d317, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d317, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d984, d317, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3348 (p : Pattern) (guard : d984 p = 1) : d318 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d318, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3346 p hg
    simpa only [d318, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d318, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3347 p hg
    simpa only [d318, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3349 (p : Pattern) (guard : d984 p = 1) : d319 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3348 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3350 (p : Pattern) (guard : d984 p = 1) : d320 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d320, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3349 p hg
    simpa only [d320, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d320, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3307 p hg
    simpa only [d320, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3351 (p : Pattern) (guard : d984 p = 1) : d321 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d321, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3345 p hg
    simpa only [d321, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d321, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d321, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3352 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3353 (p : Pattern) (guard : d915 p = 1) : d86 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3352 p hg
    simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3354 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3355 (p : Pattern) (guard : d984 p = 1) : d309 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d309, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3353 p hg
    simpa only [d984, d309, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d309, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3354 p hg
    simpa only [d984, d309, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3356 (p : Pattern) (guard : d984 p = 1) : d310 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3324 p hg
    simpa only [d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3357 (p : Pattern) (guard : d984 p = 1) : d311 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3343 p hg
    simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3356 p hg
    simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3358 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3334 p hg
    simpa only [d984, d312, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d984, d312, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3359 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3332 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
