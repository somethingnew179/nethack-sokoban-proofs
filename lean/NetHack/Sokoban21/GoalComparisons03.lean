/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons02
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC390 (pattern : Twelve) (guard : d3251 pattern = 1) : d378 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC385 pattern childGuard
    simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC100 pattern childGuard
    simpa only [d3251, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC391 (pattern : Twelve) (guard : d3252 pattern = 1) : d396 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC389 pattern childGuard
    simpa only [d3252, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC390 pattern childGuard
    simpa only [d3252, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC392 (pattern : Twelve) (guard : d3253 pattern = 1) : d405 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC387 pattern childGuard
    simpa only [d3253, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC391 pattern childGuard
    simpa only [d3253, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC393 (pattern : Twelve) (guard : d3244 pattern = 1) : d39 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC104 pattern childGuard
    simpa only [d3244, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d3244, d39, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC394 (pattern : Twelve) (guard : d3248 pattern = 1) : d39 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC393 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC107 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC395 (pattern : Twelve) (guard : d3251 pattern = 1) : d384 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC107 pattern childGuard
    simpa only [d3251, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC110 pattern childGuard
    simpa only [d3251, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC396 (pattern : Twelve) (guard : d3252 pattern = 1) : d397 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC394 pattern childGuard
    simpa only [d3252, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC395 pattern childGuard
    simpa only [d3252, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC397 (pattern : Twelve) (guard : d3251 pattern = 1) : d39 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC107 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC113 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC398 (pattern : Twelve) (guard : d0 pattern = 1) : d385 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC399 (pattern : Twelve) (guard : d3255 pattern = 1) : d398 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC397 pattern childGuard
    simpa only [d3255, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC398 pattern childGuard
    simpa only [d3255, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC400 (pattern : Twelve) (guard : d3256 pattern = 1) : d406 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC396 pattern childGuard
    simpa only [d3256, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC399 pattern childGuard
    simpa only [d3256, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC401 (pattern : Twelve) (guard : d3257 pattern = 1) : d411 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d411, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC392 pattern childGuard
    simpa only [d3257, d411, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d411, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC400 pattern childGuard
    simpa only [d3257, d411, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC402 (pattern : Twelve) (guard : d3244 pattern = 1) : d35 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC119 pattern childGuard
    simpa only [d3244, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d3244, d35, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC403 (pattern : Twelve) (guard : d3248 pattern = 1) : d35 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC402 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC123 pattern childGuard
    simpa only [d3248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC404 (pattern : Twelve) (guard : d3251 pattern = 1) : d380 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC123 pattern childGuard
    simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC126 pattern childGuard
    simpa only [d3251, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC405 (pattern : Twelve) (guard : d3252 pattern = 1) : d399 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC403 pattern childGuard
    simpa only [d3252, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC404 pattern childGuard
    simpa only [d3252, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC406 (pattern : Twelve) (guard : d3251 pattern = 1) : d35 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC123 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC129 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC407 (pattern : Twelve) (guard : d0 pattern = 1) : d378 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC408 (pattern : Twelve) (guard : d3255 pattern = 1) : d394 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC406 pattern childGuard
    simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC407 pattern childGuard
    simpa only [d3255, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC409 (pattern : Twelve) (guard : d3256 pattern = 1) : d407 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC405 pattern childGuard
    simpa only [d3256, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC408 pattern childGuard
    simpa only [d3256, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC410 (pattern : Twelve) (guard : d3260 pattern = 1) : d412 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d412, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC409 pattern childGuard
    simpa only [d3260, d412, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d412, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d412, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC411 (pattern : Twelve) (guard : d3261 pattern = 1) : d416 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d416, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC401 pattern childGuard
    simpa only [d3261, d416, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d416, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC410 pattern childGuard
    simpa only [d3261, d416, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC412 (pattern : Twelve) (guard : d3262 pattern = 1) : d419 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d419, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC381 pattern childGuard
    simpa only [d3262, d419, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d419, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC411 pattern childGuard
    simpa only [d3262, d419, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC413 (pattern : Twelve) (guard : d3265 pattern = 1) : d420 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range420 pattern).2
  change d420 pattern ≤ (0 : Int) + 6
  omega
theorem goalC414 (pattern : Twelve) (guard : d3266 pattern = 1) : d422 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d422, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC412 pattern childGuard
    simpa only [d3266, d422, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d422, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC413 pattern childGuard
    simpa only [d3266, d422, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC415 (pattern : Twelve) (guard : d3269 pattern = 1) : d420 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range420 pattern).2
  change d420 pattern ≤ (0 : Int) + 6
  omega
theorem goalC416 (pattern : Twelve) (guard : d3270 pattern = 1) : d423 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d423, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC414 pattern childGuard
    simpa only [d3270, d423, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d423, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC415 pattern childGuard
    simpa only [d3270, d423, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC417 (pattern : Twelve) (guard : d3273 pattern = 1) : d421 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range421 pattern).2
  change d421 pattern ≤ (0 : Int) + 6
  omega
theorem goalC418 (pattern : Twelve) (guard : d3274 pattern = 1) : d424 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d424, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC416 pattern childGuard
    simpa only [d3274, d424, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d424, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC417 pattern childGuard
    simpa only [d3274, d424, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC419 (pattern : Twelve) (guard : d3246 pattern = 1) : d425 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC3 pattern childGuard
    simpa only [d3246, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC156 pattern childGuard
    simpa only [d3246, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC420 (pattern : Twelve) (guard : d3249 pattern = 1) : d426 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC13 pattern childGuard
    simpa only [d3249, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC160 pattern childGuard
    simpa only [d3249, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC421 (pattern : Twelve) (guard : d3250 pattern = 1) : d444 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC419 pattern childGuard
    simpa only [d3250, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC420 pattern childGuard
    simpa only [d3250, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC422 (pattern : Twelve) (guard : d3249 pattern = 1) : d427 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC32 pattern childGuard
    simpa only [d3249, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC171 pattern childGuard
    simpa only [d3249, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC423 (pattern : Twelve) (guard : d3252 pattern = 1) : d428 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC45 pattern childGuard
    simpa only [d3252, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC174 pattern childGuard
    simpa only [d3252, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC424 (pattern : Twelve) (guard : d3253 pattern = 1) : d445 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC422 pattern childGuard
    simpa only [d3253, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC423 pattern childGuard
    simpa only [d3253, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC425 (pattern : Twelve) (guard : d3254 pattern = 1) : d455 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d455, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC421 pattern childGuard
    simpa only [d3254, d455, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d455, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC424 pattern childGuard
    simpa only [d3254, d455, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC426 (pattern : Twelve) (guard : d3249 pattern = 1) : d429 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC57 pattern childGuard
    simpa only [d3249, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC171 pattern childGuard
    simpa only [d3249, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC427 (pattern : Twelve) (guard : d3252 pattern = 1) : d430 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC64 pattern childGuard
    simpa only [d3252, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC174 pattern childGuard
    simpa only [d3252, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC428 (pattern : Twelve) (guard : d3253 pattern = 1) : d446 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC426 pattern childGuard
    simpa only [d3253, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC427 pattern childGuard
    simpa only [d3253, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC429 (pattern : Twelve) (guard : d3252 pattern = 1) : d431 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC72 pattern childGuard
    simpa only [d3252, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC185 pattern childGuard
    simpa only [d3252, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC430 (pattern : Twelve) (guard : d3255 pattern = 1) : d432 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC78 pattern childGuard
    simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC431 (pattern : Twelve) (guard : d3256 pattern = 1) : d447 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC429 pattern childGuard
    simpa only [d3256, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC430 pattern childGuard
    simpa only [d3256, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC432 (pattern : Twelve) (guard : d3257 pattern = 1) : d456 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d456, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC428 pattern childGuard
    simpa only [d3257, d456, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d456, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC431 pattern childGuard
    simpa only [d3257, d456, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC433 (pattern : Twelve) (guard : d3258 pattern = 1) : d465 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d465, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC425 pattern childGuard
    simpa only [d3258, d465, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d465, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC432 pattern childGuard
    simpa only [d3258, d465, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC434 (pattern : Twelve) (guard : d3249 pattern = 1) : d433 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC88 pattern childGuard
    simpa only [d3249, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC195 pattern childGuard
    simpa only [d3249, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC435 (pattern : Twelve) (guard : d3252 pattern = 1) : d434 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC97 pattern childGuard
    simpa only [d3252, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC198 pattern childGuard
    simpa only [d3252, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC436 (pattern : Twelve) (guard : d3253 pattern = 1) : d448 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC434 pattern childGuard
    simpa only [d3253, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC435 pattern childGuard
    simpa only [d3253, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC437 (pattern : Twelve) (guard : d3252 pattern = 1) : d435 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC108 pattern childGuard
    simpa only [d3252, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC206 pattern childGuard
    simpa only [d3252, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC438 (pattern : Twelve) (guard : d3255 pattern = 1) : d436 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC114 pattern childGuard
    simpa only [d3255, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3255, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC439 (pattern : Twelve) (guard : d3256 pattern = 1) : d449 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC437 pattern childGuard
    simpa only [d3256, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC438 pattern childGuard
    simpa only [d3256, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC440 (pattern : Twelve) (guard : d3257 pattern = 1) : d457 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d457, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC436 pattern childGuard
    simpa only [d3257, d457, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d457, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC439 pattern childGuard
    simpa only [d3257, d457, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC441 (pattern : Twelve) (guard : d3252 pattern = 1) : d437 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC124 pattern childGuard
    simpa only [d3252, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC206 pattern childGuard
    simpa only [d3252, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC442 (pattern : Twelve) (guard : d3255 pattern = 1) : d432 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC130 pattern childGuard
    simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3255, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC443 (pattern : Twelve) (guard : d3256 pattern = 1) : d450 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC441 pattern childGuard
    simpa only [d3256, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC442 pattern childGuard
    simpa only [d3256, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC444 (pattern : Twelve) (guard : d3260 pattern = 1) : d458 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d458, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC443 pattern childGuard
    simpa only [d3260, d458, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d458, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d458, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC445 (pattern : Twelve) (guard : d3261 pattern = 1) : d466 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d466, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC440 pattern childGuard
    simpa only [d3261, d466, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d466, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC444 pattern childGuard
    simpa only [d3261, d466, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC446 (pattern : Twelve) (guard : d3262 pattern = 1) : d471 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d471, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC433 pattern childGuard
    simpa only [d3262, d471, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d471, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC445 pattern childGuard
    simpa only [d3262, d471, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC447 (pattern : Twelve) (guard : d3265 pattern = 1) : d472 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range472 pattern).2
  change d472 pattern ≤ (0 : Int) + 6
  omega
theorem goalC448 (pattern : Twelve) (guard : d3266 pattern = 1) : d474 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d474, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC446 pattern childGuard
    simpa only [d3266, d474, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d474, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC447 pattern childGuard
    simpa only [d3266, d474, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC449 (pattern : Twelve) (guard : d3269 pattern = 1) : d472 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range472 pattern).2
  change d472 pattern ≤ (0 : Int) + 6
  omega
theorem goalC450 (pattern : Twelve) (guard : d3270 pattern = 1) : d475 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d475, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC448 pattern childGuard
    simpa only [d3270, d475, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d475, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC449 pattern childGuard
    simpa only [d3270, d475, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC451 (pattern : Twelve) (guard : d3273 pattern = 1) : d473 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range473 pattern).2
  change d473 pattern ≤ (0 : Int) + 6
  omega
theorem goalC452 (pattern : Twelve) (guard : d3274 pattern = 1) : d476 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d476, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC450 pattern childGuard
    simpa only [d3274, d476, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d476, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC451 pattern childGuard
    simpa only [d3274, d476, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC453 (pattern : Twelve) (guard : d1 pattern = 1) : d477 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC454 (pattern : Twelve) (guard : d1 pattern = 1) : d498 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d498, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d498, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d498, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC453 pattern childGuard
    simpa only [d498, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC455 (pattern : Twelve) (guard : d3241 pattern = 1) : d478 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d3241, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d3241, d478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC456 (pattern : Twelve) (guard : d3242 pattern = 1) : d499 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d499, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d3242, d499, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d499, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC455 pattern childGuard
    simpa only [d3242, d499, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC457 (pattern : Twelve) (guard : d3243 pattern = 1) : d532 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3243, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC454 pattern childGuard
    simpa only [d3243, d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3243, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC456 pattern childGuard
    simpa only [d3243, d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC458 (pattern : Twelve) (guard : d1867 pattern = 1) : d479 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3253 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC459 (pattern : Twelve) (guard : d3244 pattern = 1) : d500 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d500, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d500, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d500, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC458 pattern childGuard
    simpa only [d3244, d500, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC460 (pattern : Twelve) (guard : d3245 pattern = 1) : d533 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3245, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC459 pattern childGuard
    simpa only [d3245, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC461 (pattern : Twelve) (guard : d3246 pattern = 1) : d561 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC457 pattern childGuard
    simpa only [d3246, d561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC460 pattern childGuard
    simpa only [d3246, d561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC462 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) ≤ (0 : Int) + 1
  decide
theorem goalC463 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC462 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC464 (pattern : Twelve) (guard : d3244 pattern = 1) : d501 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d501, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d501, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d501, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC463 pattern childGuard
    simpa only [d3244, d501, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC465 (pattern : Twelve) (guard : d3245 pattern = 1) : d534 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC456 pattern childGuard
    simpa only [d3245, d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC464 pattern childGuard
    simpa only [d3245, d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC466 (pattern : Twelve) (guard : d1867 pattern = 1) : d481 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC14 pattern childGuard
    simpa only [d1867, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1867, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC467 (pattern : Twelve) (guard : d3244 pattern = 1) : d502 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d502, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d502, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d502, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC466 pattern childGuard
    simpa only [d3244, d502, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC468 (pattern : Twelve) (guard : d1867 pattern = 1) : d482 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7758 pattern childGuard
    simpa only [d1867, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1867, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC469 (pattern : Twelve) (guard : d3247 pattern = 1) : d503 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d503, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC468 pattern childGuard
    simpa only [d3247, d503, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d503, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d503, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC470 (pattern : Twelve) (guard : d3248 pattern = 1) : d535 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC467 pattern childGuard
    simpa only [d3248, d535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC469 pattern childGuard
    simpa only [d3248, d535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC471 (pattern : Twelve) (guard : d3249 pattern = 1) : d562 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC465 pattern childGuard
    simpa only [d3249, d562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC470 pattern childGuard
    simpa only [d3249, d562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC472 (pattern : Twelve) (guard : d3250 pattern = 1) : d588 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC461 pattern childGuard
    simpa only [d3250, d588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC471 pattern childGuard
    simpa only [d3250, d588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC473 (pattern : Twelve) (guard : d1 pattern = 1) : d483 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC474 (pattern : Twelve) (guard : d3241 pattern = 1) : d484 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10963 pattern childGuard
    simpa only [d3241, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d3241, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC475 (pattern : Twelve) (guard : d3242 pattern = 1) : d504 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d504, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC473 pattern childGuard
    simpa only [d3242, d504, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d504, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC474 pattern childGuard
    simpa only [d3242, d504, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC476 (pattern : Twelve) (guard : d3241 pattern = 1) : d485 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d3241, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d3241, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC477 (pattern : Twelve) (guard : d1867 pattern = 1) : d486 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC28 pattern childGuard
    simpa only [d1867, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1867, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC478 (pattern : Twelve) (guard : d3244 pattern = 1) : d505 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d505, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC476 pattern childGuard
    simpa only [d3244, d505, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d505, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC477 pattern childGuard
    simpa only [d3244, d505, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC479 (pattern : Twelve) (guard : d3245 pattern = 1) : d536 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC475 pattern childGuard
    simpa only [d3245, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC478 pattern childGuard
    simpa only [d3245, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC480 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d3 pattern := by
  change (2 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC481 (pattern : Twelve) (guard : d1867 pattern = 1) : d487 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC480 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC482 (pattern : Twelve) (guard : d3244 pattern = 1) : d506 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d506, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC476 pattern childGuard
    simpa only [d3244, d506, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d506, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC481 pattern childGuard
    simpa only [d3244, d506, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC483 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC35 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC484 (pattern : Twelve) (guard : d0 pattern = 1) : d170 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC485 (pattern : Twelve) (guard : d3247 pattern = 1) : d507 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d507, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC483 pattern childGuard
    simpa only [d3247, d507, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d507, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC484 pattern childGuard
    simpa only [d3247, d507, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC486 (pattern : Twelve) (guard : d3248 pattern = 1) : d537 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC482 pattern childGuard
    simpa only [d3248, d537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC485 pattern childGuard
    simpa only [d3248, d537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC487 (pattern : Twelve) (guard : d3249 pattern = 1) : d563 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC479 pattern childGuard
    simpa only [d3249, d563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC486 pattern childGuard
    simpa only [d3249, d563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC488 (pattern : Twelve) (guard : d3247 pattern = 1) : d508 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d508, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC483 pattern childGuard
    simpa only [d3247, d508, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d508, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC43 pattern childGuard
    simpa only [d3247, d508, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC489 (pattern : Twelve) (guard : d3248 pattern = 1) : d538 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC482 pattern childGuard
    simpa only [d3248, d538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC488 pattern childGuard
    simpa only [d3248, d538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC490 (pattern : Twelve) (guard : d0 pattern = 1) : d487 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC491 (pattern : Twelve) (guard : d3247 pattern = 1) : d509 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d509, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC483 pattern childGuard
    simpa only [d3247, d509, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d509, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC490 pattern childGuard
    simpa only [d3247, d509, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC492 (pattern : Twelve) (guard : d0 pattern = 1) : d503 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC493 (pattern : Twelve) (guard : d3251 pattern = 1) : d539 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC491 pattern childGuard
    simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC492 pattern childGuard
    simpa only [d3251, d539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC494 (pattern : Twelve) (guard : d3252 pattern = 1) : d564 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC489 pattern childGuard
    simpa only [d3252, d564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC493 pattern childGuard
    simpa only [d3252, d564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC495 (pattern : Twelve) (guard : d3253 pattern = 1) : d589 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC487 pattern childGuard
    simpa only [d3253, d589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC494 pattern childGuard
    simpa only [d3253, d589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC496 (pattern : Twelve) (guard : d3254 pattern = 1) : d606 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d606, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC472 pattern childGuard
    simpa only [d3254, d606, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d606, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC495 pattern childGuard
    simpa only [d3254, d606, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC497 (pattern : Twelve) (guard : d3241 pattern = 1) : d488 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d3241, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d3241, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC498 (pattern : Twelve) (guard : d3242 pattern = 1) : d510 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d510, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC473 pattern childGuard
    simpa only [d3242, d510, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d510, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC497 pattern childGuard
    simpa only [d3242, d510, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC499 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC89 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC500 (pattern : Twelve) (guard : d3244 pattern = 1) : d511 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d511, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC476 pattern childGuard
    simpa only [d3244, d511, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d511, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC499 pattern childGuard
    simpa only [d3244, d511, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC501 (pattern : Twelve) (guard : d3245 pattern = 1) : d540 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC498 pattern childGuard
    simpa only [d3245, d540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC500 pattern childGuard
    simpa only [d3245, d540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC502 (pattern : Twelve) (guard : d1866 pattern = 1) : d1 pattern ≤ (0 : Int) + d3 pattern := by
  change (1 : Int) ≤ (0 : Int) + 3
  decide
theorem goalC503 (pattern : Twelve) (guard : d1867 pattern = 1) : d479 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC502 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1867, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC504 (pattern : Twelve) (guard : d3244 pattern = 1) : d512 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d512, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC476 pattern childGuard
    simpa only [d3244, d512, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d512, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC503 pattern childGuard
    simpa only [d3244, d512, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC505 (pattern : Twelve) (guard : d0 pattern = 1) : d479 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC506 (pattern : Twelve) (guard : d3247 pattern = 1) : d513 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d513, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC483 pattern childGuard
    simpa only [d3247, d513, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d513, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC505 pattern childGuard
    simpa only [d3247, d513, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC507 (pattern : Twelve) (guard : d3248 pattern = 1) : d541 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC504 pattern childGuard
    simpa only [d3248, d541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC506 pattern childGuard
    simpa only [d3248, d541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC508 (pattern : Twelve) (guard : d3249 pattern = 1) : d565 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC501 pattern childGuard
    simpa only [d3249, d565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC507 pattern childGuard
    simpa only [d3249, d565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC509 (pattern : Twelve) (guard : d0 pattern = 1) : d480 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC510 (pattern : Twelve) (guard : d3247 pattern = 1) : d480 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC483 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC509 pattern childGuard
    simpa only [d3247, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC511 (pattern : Twelve) (guard : d3248 pattern = 1) : d542 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC500 pattern childGuard
    simpa only [d3248, d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC510 pattern childGuard
    simpa only [d3248, d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC512 (pattern : Twelve) (guard : d3252 pattern = 1) : d566 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC511 pattern childGuard
    simpa only [d3252, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC493 pattern childGuard
    simpa only [d3252, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC513 (pattern : Twelve) (guard : d3253 pattern = 1) : d590 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC508 pattern childGuard
    simpa only [d3253, d590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC512 pattern childGuard
    simpa only [d3253, d590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC514 (pattern : Twelve) (guard : d3241 pattern = 1) : d489 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d3241, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d3241, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC515 (pattern : Twelve) (guard : d1866 pattern = 1) : d2 pattern ≤ (0 : Int) + d5 pattern := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem goalC516 (pattern : Twelve) (guard : d1867 pattern = 1) : d487 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC515 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1867, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC517 (pattern : Twelve) (guard : d3244 pattern = 1) : d514 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d514, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC514 pattern childGuard
    simpa only [d3244, d514, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d514, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC516 pattern childGuard
    simpa only [d3244, d514, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC518 (pattern : Twelve) (guard : d1866 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem goalC519 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC518 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
