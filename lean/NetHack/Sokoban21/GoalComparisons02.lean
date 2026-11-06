/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons01
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC260 (pattern : Twelve) (guard : d3251 pattern = 1) : d241 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC99 pattern childGuard
    simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC261 (pattern : Twelve) (guard : d3252 pattern = 1) : d265 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC258 pattern childGuard
    simpa only [d3252, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC260 pattern childGuard
    simpa only [d3252, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC262 (pattern : Twelve) (guard : d3253 pattern = 1) : d276 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC259 pattern childGuard
    simpa only [d3253, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC261 pattern childGuard
    simpa only [d3253, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC263 (pattern : Twelve) (guard : d3248 pattern = 1) : d249 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC106 pattern childGuard
    simpa only [d3248, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC203 pattern childGuard
    simpa only [d3248, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC264 (pattern : Twelve) (guard : d3251 pattern = 1) : d250 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC109 pattern childGuard
    simpa only [d3251, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3251, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC265 (pattern : Twelve) (guard : d3252 pattern = 1) : d266 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC263 pattern childGuard
    simpa only [d3252, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC264 pattern childGuard
    simpa only [d3252, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC266 (pattern : Twelve) (guard : d0 pattern = 1) : d251 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC267 (pattern : Twelve) (guard : d3255 pattern = 1) : d267 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC264 pattern childGuard
    simpa only [d3255, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC266 pattern childGuard
    simpa only [d3255, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC268 (pattern : Twelve) (guard : d3256 pattern = 1) : d277 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC265 pattern childGuard
    simpa only [d3256, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC267 pattern childGuard
    simpa only [d3256, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC269 (pattern : Twelve) (guard : d3257 pattern = 1) : d286 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d286, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC262 pattern childGuard
    simpa only [d3257, d286, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d286, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC268 pattern childGuard
    simpa only [d3257, d286, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC270 (pattern : Twelve) (guard : d3248 pattern = 1) : d252 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC121 pattern childGuard
    simpa only [d3248, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC203 pattern childGuard
    simpa only [d3248, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC271 (pattern : Twelve) (guard : d3251 pattern = 1) : d246 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC125 pattern childGuard
    simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC272 (pattern : Twelve) (guard : d3252 pattern = 1) : d268 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC270 pattern childGuard
    simpa only [d3252, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC271 pattern childGuard
    simpa only [d3252, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC273 (pattern : Twelve) (guard : d0 pattern = 1) : d241 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC274 (pattern : Twelve) (guard : d3255 pattern = 1) : d263 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC271 pattern childGuard
    simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC273 pattern childGuard
    simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC275 (pattern : Twelve) (guard : d3256 pattern = 1) : d278 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC272 pattern childGuard
    simpa only [d3256, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC274 pattern childGuard
    simpa only [d3256, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC276 (pattern : Twelve) (guard : d3260 pattern = 1) : d287 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d287, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC275 pattern childGuard
    simpa only [d3260, d287, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d287, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d287, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC277 (pattern : Twelve) (guard : d3261 pattern = 1) : d294 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d294, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC269 pattern childGuard
    simpa only [d3261, d294, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d294, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC276 pattern childGuard
    simpa only [d3261, d294, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC278 (pattern : Twelve) (guard : d3262 pattern = 1) : d297 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d297, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC256 pattern childGuard
    simpa only [d3262, d297, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d297, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC277 pattern childGuard
    simpa only [d3262, d297, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC279 (pattern : Twelve) (guard : d3265 pattern = 1) : d298 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range298 pattern).2
  change d298 pattern ≤ (0 : Int) + 6
  omega
theorem goalC280 (pattern : Twelve) (guard : d3266 pattern = 1) : d300 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d300, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC278 pattern childGuard
    simpa only [d3266, d300, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d300, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC279 pattern childGuard
    simpa only [d3266, d300, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC281 (pattern : Twelve) (guard : d3269 pattern = 1) : d301 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range301 pattern).2
  change d301 pattern ≤ (0 : Int) + 6
  omega
theorem goalC282 (pattern : Twelve) (guard : d3270 pattern = 1) : d302 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d302, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC280 pattern childGuard
    simpa only [d3270, d302, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d302, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC281 pattern childGuard
    simpa only [d3270, d302, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC283 (pattern : Twelve) (guard : d3273 pattern = 1) : d301 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range301 pattern).2
  change d301 pattern ≤ (0 : Int) + 6
  omega
theorem goalC284 (pattern : Twelve) (guard : d3274 pattern = 1) : d303 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d303, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC282 pattern childGuard
    simpa only [d3274, d303, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d303, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC283 pattern childGuard
    simpa only [d3274, d303, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC285 (pattern : Twelve) (guard : d3250 pattern = 1) : d304 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC9 pattern childGuard
    simpa only [d3250, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC161 pattern childGuard
    simpa only [d3250, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC286 (pattern : Twelve) (guard : d3253 pattern = 1) : d305 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC41 pattern childGuard
    simpa only [d3253, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC175 pattern childGuard
    simpa only [d3253, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC287 (pattern : Twelve) (guard : d3254 pattern = 1) : d320 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d320, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC285 pattern childGuard
    simpa only [d3254, d320, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d320, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC286 pattern childGuard
    simpa only [d3254, d320, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC288 (pattern : Twelve) (guard : d3253 pattern = 1) : d306 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC62 pattern childGuard
    simpa only [d3253, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC175 pattern childGuard
    simpa only [d3253, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC289 (pattern : Twelve) (guard : d3256 pattern = 1) : d307 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC76 pattern childGuard
    simpa only [d3256, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC187 pattern childGuard
    simpa only [d3256, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC290 (pattern : Twelve) (guard : d3257 pattern = 1) : d321 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d321, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC288 pattern childGuard
    simpa only [d3257, d321, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d321, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC289 pattern childGuard
    simpa only [d3257, d321, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC291 (pattern : Twelve) (guard : d3258 pattern = 1) : d332 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d332, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC287 pattern childGuard
    simpa only [d3258, d332, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d332, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC290 pattern childGuard
    simpa only [d3258, d332, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC292 (pattern : Twelve) (guard : d3253 pattern = 1) : d308 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC95 pattern childGuard
    simpa only [d3253, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC199 pattern childGuard
    simpa only [d3253, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC293 (pattern : Twelve) (guard : d3256 pattern = 1) : d309 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC112 pattern childGuard
    simpa only [d3256, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC208 pattern childGuard
    simpa only [d3256, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC294 (pattern : Twelve) (guard : d3257 pattern = 1) : d322 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d322, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC292 pattern childGuard
    simpa only [d3257, d322, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d322, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC293 pattern childGuard
    simpa only [d3257, d322, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC295 (pattern : Twelve) (guard : d3256 pattern = 1) : d310 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC128 pattern childGuard
    simpa only [d3256, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC208 pattern childGuard
    simpa only [d3256, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC296 (pattern : Twelve) (guard : d3260 pattern = 1) : d323 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d323, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC295 pattern childGuard
    simpa only [d3260, d323, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d323, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d323, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC297 (pattern : Twelve) (guard : d3261 pattern = 1) : d333 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d333, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC294 pattern childGuard
    simpa only [d3261, d333, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d333, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC296 pattern childGuard
    simpa only [d3261, d333, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC298 (pattern : Twelve) (guard : d3262 pattern = 1) : d338 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d338, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC291 pattern childGuard
    simpa only [d3262, d338, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d338, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC297 pattern childGuard
    simpa only [d3262, d338, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC299 (pattern : Twelve) (guard : d3265 pattern = 1) : d339 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range339 pattern).2
  change d339 pattern ≤ (0 : Int) + 6
  omega
theorem goalC300 (pattern : Twelve) (guard : d3266 pattern = 1) : d341 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d341, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC298 pattern childGuard
    simpa only [d3266, d341, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d341, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC299 pattern childGuard
    simpa only [d3266, d341, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC301 (pattern : Twelve) (guard : d3269 pattern = 1) : d342 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range342 pattern).2
  change d342 pattern ≤ (0 : Int) + 6
  omega
theorem goalC302 (pattern : Twelve) (guard : d3270 pattern = 1) : d343 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d343, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC300 pattern childGuard
    simpa only [d3270, d343, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d343, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC301 pattern childGuard
    simpa only [d3270, d343, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC303 (pattern : Twelve) (guard : d3273 pattern = 1) : d342 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range342 pattern).2
  change d342 pattern ≤ (0 : Int) + 6
  omega
theorem goalC304 (pattern : Twelve) (guard : d3274 pattern = 1) : d344 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d344, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC302 pattern childGuard
    simpa only [d3274, d344, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d344, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC303 pattern childGuard
    simpa only [d3274, d344, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC305 (pattern : Twelve) (guard : d3262 pattern = 1) : d345 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d345, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d3262, d345, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d345, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC212 pattern childGuard
    simpa only [d3262, d345, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC306 (pattern : Twelve) (guard : d3265 pattern = 1) : d346 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range346 pattern).2
  change d346 pattern ≤ (0 : Int) + 6
  omega
theorem goalC307 (pattern : Twelve) (guard : d3266 pattern = 1) : d348 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d348, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC305 pattern childGuard
    simpa only [d3266, d348, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d348, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC306 pattern childGuard
    simpa only [d3266, d348, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC308 (pattern : Twelve) (guard : d3269 pattern = 1) : d349 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range349 pattern).2
  change d349 pattern ≤ (0 : Int) + 6
  omega
theorem goalC309 (pattern : Twelve) (guard : d3270 pattern = 1) : d350 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d350, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC307 pattern childGuard
    simpa only [d3270, d350, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d350, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC308 pattern childGuard
    simpa only [d3270, d350, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC310 (pattern : Twelve) (guard : d3273 pattern = 1) : d349 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range349 pattern).2
  change d349 pattern ≤ (0 : Int) + 6
  omega
theorem goalC311 (pattern : Twelve) (guard : d3274 pattern = 1) : d351 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d351, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC309 pattern childGuard
    simpa only [d3274, d351, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d351, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC310 pattern childGuard
    simpa only [d3274, d351, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC312 (pattern : Twelve) (guard : d3254 pattern = 1) : d352 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d352, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC23 pattern childGuard
    simpa only [d3254, d352, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d352, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC176 pattern childGuard
    simpa only [d3254, d352, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC313 (pattern : Twelve) (guard : d3257 pattern = 1) : d353 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d353, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC66 pattern childGuard
    simpa only [d3257, d353, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d353, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC188 pattern childGuard
    simpa only [d3257, d353, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC314 (pattern : Twelve) (guard : d3258 pattern = 1) : d358 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d358, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC312 pattern childGuard
    simpa only [d3258, d358, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d358, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC313 pattern childGuard
    simpa only [d3258, d358, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC315 (pattern : Twelve) (guard : d3242 pattern = 1) : d0 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d3242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC67 pattern childGuard
    simpa only [d3242, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC316 (pattern : Twelve) (guard : d3244 pattern = 1) : d0 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC53 pattern childGuard
    simpa only [d3244, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC70 pattern childGuard
    simpa only [d3244, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC317 (pattern : Twelve) (guard : d3245 pattern = 1) : d0 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC315 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC316 pattern childGuard
    simpa only [d3245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC318 (pattern : Twelve) (guard : d1867 pattern = 1) : d1 pattern ≤ (0 : Int) + d4 pattern := by
  change (1 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC319 (pattern : Twelve) (guard : d3244 pattern = 1) : d26 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d26, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC53 pattern childGuard
    simpa only [d3244, d26, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d26, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC318 pattern childGuard
    simpa only [d3244, d26, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC320 (pattern : Twelve) (guard : d3247 pattern = 1) : d27 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d27, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d3247, d27, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d27, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4652 pattern childGuard
    simpa only [d3247, d27, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC321 (pattern : Twelve) (guard : d3248 pattern = 1) : d50 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC319 pattern childGuard
    simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC320 pattern childGuard
    simpa only [d3248, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC322 (pattern : Twelve) (guard : d3249 pattern = 1) : d72 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC317 pattern childGuard
    simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC321 pattern childGuard
    simpa only [d3249, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC323 (pattern : Twelve) (guard : d3247 pattern = 1) : d0 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC55 pattern childGuard
    simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3323 pattern childGuard
    simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC324 (pattern : Twelve) (guard : d3248 pattern = 1) : d0 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC316 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC323 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC325 (pattern : Twelve) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC326 (pattern : Twelve) (guard : d3247 pattern = 1) : d28 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d28, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d3247, d28, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d28, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC325 pattern childGuard
    simpa only [d3247, d28, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC327 (pattern : Twelve) (guard : d3251 pattern = 1) : d51 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC326 pattern childGuard
    simpa only [d3251, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC100 pattern childGuard
    simpa only [d3251, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC328 (pattern : Twelve) (guard : d3252 pattern = 1) : d73 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC324 pattern childGuard
    simpa only [d3252, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC327 pattern childGuard
    simpa only [d3252, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC329 (pattern : Twelve) (guard : d3253 pattern = 1) : d91 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC322 pattern childGuard
    simpa only [d3253, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC328 pattern childGuard
    simpa only [d3253, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC330 (pattern : Twelve) (guard : d3257 pattern = 1) : d354 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d354, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC329 pattern childGuard
    simpa only [d3257, d354, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d354, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC209 pattern childGuard
    simpa only [d3257, d354, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC331 (pattern : Twelve) (guard : d1867 pattern = 1) : d0 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range0 pattern).2
  change d0 pattern ≤ (0 : Int) + 6
  omega
theorem goalC332 (pattern : Twelve) (guard : d3244 pattern = 1) : d0 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC119 pattern childGuard
    simpa only [d3244, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC331 pattern childGuard
    simpa only [d3244, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC333 (pattern : Twelve) (guard : d3247 pattern = 1) : d0 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC122 pattern childGuard
    simpa only [d3247, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d3247, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC334 (pattern : Twelve) (guard : d3248 pattern = 1) : d0 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC332 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC333 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC335 (pattern : Twelve) (guard : d3247 pattern = 1) : d26 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC122 pattern childGuard
    simpa only [d3247, d26, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d3247, d26, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC336 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC337 (pattern : Twelve) (guard : d3251 pattern = 1) : d50 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC335 pattern childGuard
    simpa only [d3251, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC336 pattern childGuard
    simpa only [d3251, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC338 (pattern : Twelve) (guard : d3252 pattern = 1) : d72 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC334 pattern childGuard
    simpa only [d3252, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC337 pattern childGuard
    simpa only [d3252, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC339 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC340 (pattern : Twelve) (guard : d3251 pattern = 1) : d0 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC333 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC339 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC341 (pattern : Twelve) (guard : d3255 pattern = 1) : d76 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC340 pattern childGuard
    simpa only [d3255, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC131 pattern childGuard
    simpa only [d3255, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC342 (pattern : Twelve) (guard : d3256 pattern = 1) : d93 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC338 pattern childGuard
    simpa only [d3256, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC341 pattern childGuard
    simpa only [d3256, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC343 (pattern : Twelve) (guard : d3260 pattern = 1) : d355 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d355, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC342 pattern childGuard
    simpa only [d3260, d355, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d355, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d355, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC344 (pattern : Twelve) (guard : d3261 pattern = 1) : d359 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d359, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC330 pattern childGuard
    simpa only [d3261, d359, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d359, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC343 pattern childGuard
    simpa only [d3261, d359, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC345 (pattern : Twelve) (guard : d3262 pattern = 1) : d361 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d361, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC314 pattern childGuard
    simpa only [d3262, d361, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d361, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC344 pattern childGuard
    simpa only [d3262, d361, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC346 (pattern : Twelve) (guard : d3265 pattern = 1) : d356 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range356 pattern).2
  change d356 pattern ≤ (0 : Int) + 6
  omega
theorem goalC347 (pattern : Twelve) (guard : d3266 pattern = 1) : d362 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d362, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC345 pattern childGuard
    simpa only [d3266, d362, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d362, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC346 pattern childGuard
    simpa only [d3266, d362, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC348 (pattern : Twelve) (guard : d3269 pattern = 1) : d363 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range363 pattern).2
  change d363 pattern ≤ (0 : Int) + 6
  omega
theorem goalC349 (pattern : Twelve) (guard : d3270 pattern = 1) : d364 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d364, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC347 pattern childGuard
    simpa only [d3270, d364, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d364, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC348 pattern childGuard
    simpa only [d3270, d364, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC350 (pattern : Twelve) (guard : d3273 pattern = 1) : d363 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range363 pattern).2
  change d363 pattern ≤ (0 : Int) + 6
  omega
theorem goalC351 (pattern : Twelve) (guard : d3274 pattern = 1) : d365 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d365, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC349 pattern childGuard
    simpa only [d3274, d365, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d365, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC350 pattern childGuard
    simpa only [d3274, d365, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC352 (pattern : Twelve) (guard : d3244 pattern = 1) : d366 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d366, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC5 pattern childGuard
    simpa only [d3244, d366, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d366, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC154 pattern childGuard
    simpa only [d3244, d366, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC353 (pattern : Twelve) (guard : d3245 pattern = 1) : d372 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3245, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC352 pattern childGuard
    simpa only [d3245, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC354 (pattern : Twelve) (guard : d3246 pattern = 1) : d389 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC152 pattern childGuard
    simpa only [d3246, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC353 pattern childGuard
    simpa only [d3246, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC355 (pattern : Twelve) (guard : d3244 pattern = 1) : d367 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d367, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC10 pattern childGuard
    simpa only [d3244, d367, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d367, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC154 pattern childGuard
    simpa only [d3244, d367, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC356 (pattern : Twelve) (guard : d3245 pattern = 1) : d373 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3245, d373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC355 pattern childGuard
    simpa only [d3245, d373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC357 (pattern : Twelve) (guard : d3248 pattern = 1) : d374 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC352 pattern childGuard
    simpa only [d3248, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC20 pattern childGuard
    simpa only [d3248, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC358 (pattern : Twelve) (guard : d3249 pattern = 1) : d390 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC356 pattern childGuard
    simpa only [d3249, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC357 pattern childGuard
    simpa only [d3249, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC359 (pattern : Twelve) (guard : d3250 pattern = 1) : d402 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC354 pattern childGuard
    simpa only [d3250, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC358 pattern childGuard
    simpa only [d3250, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC360 (pattern : Twelve) (guard : d3242 pattern = 1) : d368 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d368, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d3242, d368, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d368, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC163 pattern childGuard
    simpa only [d3242, d368, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC361 (pattern : Twelve) (guard : d3244 pattern = 1) : d369 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d369, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC26 pattern childGuard
    simpa only [d3244, d369, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d369, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC166 pattern childGuard
    simpa only [d3244, d369, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC362 (pattern : Twelve) (guard : d3245 pattern = 1) : d375 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC360 pattern childGuard
    simpa only [d3245, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC361 pattern childGuard
    simpa only [d3245, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC363 (pattern : Twelve) (guard : d3247 pattern = 1) : d36 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d36, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC37 pattern childGuard
    simpa only [d3247, d36, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d36, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d3247, d36, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC364 (pattern : Twelve) (guard : d3248 pattern = 1) : d376 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC361 pattern childGuard
    simpa only [d3248, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC363 pattern childGuard
    simpa only [d3248, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC365 (pattern : Twelve) (guard : d3249 pattern = 1) : d391 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC362 pattern childGuard
    simpa only [d3249, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC364 pattern childGuard
    simpa only [d3249, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC366 (pattern : Twelve) (guard : d3247 pattern = 1) : d35 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d35, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC42 pattern childGuard
    simpa only [d3247, d35, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d35, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d3247, d35, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC367 (pattern : Twelve) (guard : d3248 pattern = 1) : d377 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC361 pattern childGuard
    simpa only [d3248, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC366 pattern childGuard
    simpa only [d3248, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC368 (pattern : Twelve) (guard : d3251 pattern = 1) : d378 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC363 pattern childGuard
    simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC48 pattern childGuard
    simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC369 (pattern : Twelve) (guard : d3252 pattern = 1) : d392 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC367 pattern childGuard
    simpa only [d3252, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC368 pattern childGuard
    simpa only [d3252, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC370 (pattern : Twelve) (guard : d3253 pattern = 1) : d403 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC365 pattern childGuard
    simpa only [d3253, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC369 pattern childGuard
    simpa only [d3253, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC371 (pattern : Twelve) (guard : d3254 pattern = 1) : d409 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d409, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC359 pattern childGuard
    simpa only [d3254, d409, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d409, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC370 pattern childGuard
    simpa only [d3254, d409, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC372 (pattern : Twelve) (guard : d3244 pattern = 1) : d33 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d33, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC67 pattern childGuard
    simpa only [d3244, d33, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d33, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC179 pattern childGuard
    simpa only [d3244, d33, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC373 (pattern : Twelve) (guard : d3248 pattern = 1) : d379 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC372 pattern childGuard
    simpa only [d3248, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC71 pattern childGuard
    simpa only [d3248, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC374 (pattern : Twelve) (guard : d3251 pattern = 1) : d380 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC71 pattern childGuard
    simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC74 pattern childGuard
    simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC375 (pattern : Twelve) (guard : d3252 pattern = 1) : d393 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC373 pattern childGuard
    simpa only [d3252, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC374 pattern childGuard
    simpa only [d3252, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC376 (pattern : Twelve) (guard : d3251 pattern = 1) : d35 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC71 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC77 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC377 (pattern : Twelve) (guard : d0 pattern = 1) : d378 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC378 (pattern : Twelve) (guard : d3255 pattern = 1) : d394 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC376 pattern childGuard
    simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC377 pattern childGuard
    simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC379 (pattern : Twelve) (guard : d3256 pattern = 1) : d404 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC375 pattern childGuard
    simpa only [d3256, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC378 pattern childGuard
    simpa only [d3256, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC380 (pattern : Twelve) (guard : d3257 pattern = 1) : d410 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d410, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC370 pattern childGuard
    simpa only [d3257, d410, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d410, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC379 pattern childGuard
    simpa only [d3257, d410, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC381 (pattern : Twelve) (guard : d3258 pattern = 1) : d415 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d415, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC371 pattern childGuard
    simpa only [d3258, d415, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d415, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC380 pattern childGuard
    simpa only [d3258, d415, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC382 (pattern : Twelve) (guard : d3242 pattern = 1) : d370 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d370, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d3242, d370, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d370, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC178 pattern childGuard
    simpa only [d3242, d370, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC383 (pattern : Twelve) (guard : d3244 pattern = 1) : d371 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d371, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC53 pattern childGuard
    simpa only [d3244, d371, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d371, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC181 pattern childGuard
    simpa only [d3244, d371, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC384 (pattern : Twelve) (guard : d3245 pattern = 1) : d381 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC382 pattern childGuard
    simpa only [d3245, d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC383 pattern childGuard
    simpa only [d3245, d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC385 (pattern : Twelve) (guard : d3247 pattern = 1) : d36 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d36, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d3247, d36, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d36, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d3247, d36, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC386 (pattern : Twelve) (guard : d3248 pattern = 1) : d382 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC383 pattern childGuard
    simpa only [d3248, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC385 pattern childGuard
    simpa only [d3248, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC387 (pattern : Twelve) (guard : d3249 pattern = 1) : d395 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC384 pattern childGuard
    simpa only [d3249, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC386 pattern childGuard
    simpa only [d3249, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC388 (pattern : Twelve) (guard : d3247 pattern = 1) : d35 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d35, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC55 pattern childGuard
    simpa only [d3247, d35, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d35, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d3247, d35, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC389 (pattern : Twelve) (guard : d3248 pattern = 1) : d383 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC383 pattern childGuard
    simpa only [d3248, d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC388 pattern childGuard
    simpa only [d3248, d383, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
