/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons00
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC130 (pattern : Twelve) (guard : d3251 pattern = 1) : d56 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC125 pattern childGuard
    simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC129 pattern childGuard
    simpa only [d3251, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC131 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC132 (pattern : Twelve) (guard : d3255 pattern = 1) : d78 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC130 pattern childGuard
    simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC131 pattern childGuard
    simpa only [d3255, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC133 (pattern : Twelve) (guard : d3256 pattern = 1) : d94 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC128 pattern childGuard
    simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC132 pattern childGuard
    simpa only [d3256, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC134 (pattern : Twelve) (guard : d3259 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC135 (pattern : Twelve) (guard : d3260 pattern = 1) : d105 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d105, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC133 pattern childGuard
    simpa only [d3260, d105, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d105, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d105, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC136 (pattern : Twelve) (guard : d3261 pattern = 1) : d111 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d111, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC118 pattern childGuard
    simpa only [d3261, d111, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d111, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC135 pattern childGuard
    simpa only [d3261, d111, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC137 (pattern : Twelve) (guard : d3262 pattern = 1) : d114 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d114, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC83 pattern childGuard
    simpa only [d3262, d114, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d114, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC136 pattern childGuard
    simpa only [d3262, d114, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC138 (pattern : Twelve) (guard : d3265 pattern = 1) : d115 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range115 pattern).2
  change d115 pattern ≤ (0 : Int) + 6
  omega
theorem goalC139 (pattern : Twelve) (guard : d3266 pattern = 1) : d116 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d116, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC137 pattern childGuard
    simpa only [d3266, d116, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d116, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC138 pattern childGuard
    simpa only [d3266, d116, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC140 (pattern : Twelve) (guard : d3269 pattern = 1) : d116 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range116 pattern).2
  change d116 pattern ≤ (0 : Int) + 6
  omega
theorem goalC141 (pattern : Twelve) (guard : d3270 pattern = 1) : d116 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC139 pattern childGuard
    simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC140 pattern childGuard
    simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC142 (pattern : Twelve) (guard : d3273 pattern = 1) : d116 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range116 pattern).2
  change d116 pattern ≤ (0 : Int) + 6
  omega
theorem goalC143 (pattern : Twelve) (guard : d3274 pattern = 1) : d116 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC141 pattern childGuard
    simpa only [d3274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC142 pattern childGuard
    simpa only [d3274, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC144 (pattern : Twelve) (guard : d3265 pattern = 1) : d114 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range114 pattern).2
  change d114 pattern ≤ (0 : Int) + 6
  omega
theorem goalC145 (pattern : Twelve) (guard : d3266 pattern = 1) : d114 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC137 pattern childGuard
    simpa only [d3266, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC144 pattern childGuard
    simpa only [d3266, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC146 (pattern : Twelve) (guard : d3269 pattern = 1) : d114 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range114 pattern).2
  change d114 pattern ≤ (0 : Int) + 6
  omega
theorem goalC147 (pattern : Twelve) (guard : d3270 pattern = 1) : d114 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC145 pattern childGuard
    simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC146 pattern childGuard
    simpa only [d3270, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC148 (pattern : Twelve) (guard : d3273 pattern = 1) : d155 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range155 pattern).2
  change d155 pattern ≤ (0 : Int) + 6
  omega
theorem goalC149 (pattern : Twelve) (guard : d3274 pattern = 1) : d156 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d156, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC147 pattern childGuard
    simpa only [d3274, d156, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d156, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC148 pattern childGuard
    simpa only [d3274, d156, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC150 (pattern : Twelve) (guard : d3241 pattern = 1) : d161 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d3241, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d3241, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC151 (pattern : Twelve) (guard : d3242 pattern = 1) : d171 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d3242, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC150 pattern childGuard
    simpa only [d3242, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC152 (pattern : Twelve) (guard : d3243 pattern = 1) : d184 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3243, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d3243, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3243, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3243, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC153 (pattern : Twelve) (guard : d3241 pattern = 1) : d162 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d3241, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d3241, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC154 (pattern : Twelve) (guard : d1867 pattern = 1) : d163 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d1867, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1867, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC155 (pattern : Twelve) (guard : d3244 pattern = 1) : d172 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC153 pattern childGuard
    simpa only [d3244, d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC154 pattern childGuard
    simpa only [d3244, d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC156 (pattern : Twelve) (guard : d3245 pattern = 1) : d185 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3245, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC155 pattern childGuard
    simpa only [d3245, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC157 (pattern : Twelve) (guard : d3246 pattern = 1) : d197 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC152 pattern childGuard
    simpa only [d3246, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC156 pattern childGuard
    simpa only [d3246, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC158 (pattern : Twelve) (guard : d1867 pattern = 1) : d164 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1867, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1867, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC159 (pattern : Twelve) (guard : d3247 pattern = 1) : d173 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d173, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC158 pattern childGuard
    simpa only [d3247, d173, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d173, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d173, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC160 (pattern : Twelve) (guard : d3248 pattern = 1) : d186 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC155 pattern childGuard
    simpa only [d3248, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC159 pattern childGuard
    simpa only [d3248, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC161 (pattern : Twelve) (guard : d3249 pattern = 1) : d198 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC156 pattern childGuard
    simpa only [d3249, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC160 pattern childGuard
    simpa only [d3249, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC162 (pattern : Twelve) (guard : d3250 pattern = 1) : d207 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC157 pattern childGuard
    simpa only [d3250, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC161 pattern childGuard
    simpa only [d3250, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC163 (pattern : Twelve) (guard : d3241 pattern = 1) : d165 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d3241, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d3241, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC164 (pattern : Twelve) (guard : d3242 pattern = 1) : d174 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d174, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d3242, d174, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d174, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC163 pattern childGuard
    simpa only [d3242, d174, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC165 (pattern : Twelve) (guard : d3241 pattern = 1) : d166 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d3241, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d3241, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC166 (pattern : Twelve) (guard : d1867 pattern = 1) : d167 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7815 pattern childGuard
    simpa only [d1867, d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1867, d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC167 (pattern : Twelve) (guard : d3244 pattern = 1) : d175 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d175, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC165 pattern childGuard
    simpa only [d3244, d175, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d175, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC166 pattern childGuard
    simpa only [d3244, d175, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC168 (pattern : Twelve) (guard : d3245 pattern = 1) : d187 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC164 pattern childGuard
    simpa only [d3245, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC167 pattern childGuard
    simpa only [d3245, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC169 (pattern : Twelve) (guard : d1867 pattern = 1) : d168 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7761 pattern childGuard
    simpa only [d1867, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1867, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC170 (pattern : Twelve) (guard : d3247 pattern = 1) : d176 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d176, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC169 pattern childGuard
    simpa only [d3247, d176, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d176, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d3247, d176, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC171 (pattern : Twelve) (guard : d3248 pattern = 1) : d188 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC167 pattern childGuard
    simpa only [d3248, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC170 pattern childGuard
    simpa only [d3248, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC172 (pattern : Twelve) (guard : d3249 pattern = 1) : d199 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC168 pattern childGuard
    simpa only [d3249, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC171 pattern childGuard
    simpa only [d3249, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC173 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC174 (pattern : Twelve) (guard : d3251 pattern = 1) : d189 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC170 pattern childGuard
    simpa only [d3251, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3251, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC175 (pattern : Twelve) (guard : d3252 pattern = 1) : d200 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC171 pattern childGuard
    simpa only [d3252, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC174 pattern childGuard
    simpa only [d3252, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC176 (pattern : Twelve) (guard : d3253 pattern = 1) : d208 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC172 pattern childGuard
    simpa only [d3253, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC175 pattern childGuard
    simpa only [d3253, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC177 (pattern : Twelve) (guard : d3254 pattern = 1) : d212 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d212, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC162 pattern childGuard
    simpa only [d3254, d212, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d212, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC176 pattern childGuard
    simpa only [d3254, d212, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC178 (pattern : Twelve) (guard : d3241 pattern = 1) : d169 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d3241, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d3241, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC179 (pattern : Twelve) (guard : d1867 pattern = 1) : d22 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d1867, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1867, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC180 (pattern : Twelve) (guard : d3244 pattern = 1) : d177 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d177, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC178 pattern childGuard
    simpa only [d3244, d177, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d177, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC179 pattern childGuard
    simpa only [d3244, d177, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC181 (pattern : Twelve) (guard : d1867 pattern = 1) : d170 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7825 pattern childGuard
    simpa only [d1867, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1867, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC182 (pattern : Twelve) (guard : d3247 pattern = 1) : d178 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d178, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC181 pattern childGuard
    simpa only [d3247, d178, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d178, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d3247, d178, d3282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC183 (pattern : Twelve) (guard : d3248 pattern = 1) : d190 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC180 pattern childGuard
    simpa only [d3248, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC182 pattern childGuard
    simpa only [d3248, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC184 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC185 (pattern : Twelve) (guard : d3251 pattern = 1) : d191 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC182 pattern childGuard
    simpa only [d3251, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3251, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC186 (pattern : Twelve) (guard : d3252 pattern = 1) : d201 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC183 pattern childGuard
    simpa only [d3252, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC185 pattern childGuard
    simpa only [d3252, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC187 (pattern : Twelve) (guard : d3255 pattern = 1) : d202 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC185 pattern childGuard
    simpa only [d3255, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3255, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC188 (pattern : Twelve) (guard : d3256 pattern = 1) : d209 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC186 pattern childGuard
    simpa only [d3256, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC187 pattern childGuard
    simpa only [d3256, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC189 (pattern : Twelve) (guard : d3257 pattern = 1) : d213 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d213, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC176 pattern childGuard
    simpa only [d3257, d213, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d213, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC188 pattern childGuard
    simpa only [d3257, d213, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC190 (pattern : Twelve) (guard : d3258 pattern = 1) : d216 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d216, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC177 pattern childGuard
    simpa only [d3258, d216, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d216, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC189 pattern childGuard
    simpa only [d3258, d216, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC191 (pattern : Twelve) (guard : d3242 pattern = 1) : d179 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3242, d179, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d3242, d179, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3242, d179, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC178 pattern childGuard
    simpa only [d3242, d179, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC192 (pattern : Twelve) (guard : d3244 pattern = 1) : d180 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d180, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC163 pattern childGuard
    simpa only [d3244, d180, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d180, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC181 pattern childGuard
    simpa only [d3244, d180, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC193 (pattern : Twelve) (guard : d3245 pattern = 1) : d192 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC191 pattern childGuard
    simpa only [d3245, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC192 pattern childGuard
    simpa only [d3245, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC194 (pattern : Twelve) (guard : d3247 pattern = 1) : d181 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d181, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC166 pattern childGuard
    simpa only [d3247, d181, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d181, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d3247, d181, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC195 (pattern : Twelve) (guard : d3248 pattern = 1) : d193 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC192 pattern childGuard
    simpa only [d3248, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC194 pattern childGuard
    simpa only [d3248, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC196 (pattern : Twelve) (guard : d3249 pattern = 1) : d203 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC193 pattern childGuard
    simpa only [d3249, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC195 pattern childGuard
    simpa only [d3249, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC197 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC198 (pattern : Twelve) (guard : d3251 pattern = 1) : d194 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC194 pattern childGuard
    simpa only [d3251, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d3251, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC199 (pattern : Twelve) (guard : d3252 pattern = 1) : d204 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC195 pattern childGuard
    simpa only [d3252, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC198 pattern childGuard
    simpa only [d3252, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC200 (pattern : Twelve) (guard : d3253 pattern = 1) : d210 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC196 pattern childGuard
    simpa only [d3253, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC199 pattern childGuard
    simpa only [d3253, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC201 (pattern : Twelve) (guard : d3241 pattern = 1) : d118 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3241, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d3241, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d3241, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d3241, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC202 (pattern : Twelve) (guard : d3244 pattern = 1) : d182 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d3241 pattern = 1 := by simpa only [d3244, d182, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC201 pattern childGuard
    simpa only [d3244, d182, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3244, d182, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d3244, d182, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC203 (pattern : Twelve) (guard : d3247 pattern = 1) : d183 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d183, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC179 pattern childGuard
    simpa only [d3247, d183, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d183, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3247, d183, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC204 (pattern : Twelve) (guard : d3248 pattern = 1) : d195 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC202 pattern childGuard
    simpa only [d3248, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC203 pattern childGuard
    simpa only [d3248, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC205 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC206 (pattern : Twelve) (guard : d3251 pattern = 1) : d196 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC203 pattern childGuard
    simpa only [d3251, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3251, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC207 (pattern : Twelve) (guard : d3252 pattern = 1) : d205 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC204 pattern childGuard
    simpa only [d3252, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC206 pattern childGuard
    simpa only [d3252, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC208 (pattern : Twelve) (guard : d3255 pattern = 1) : d206 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC206 pattern childGuard
    simpa only [d3255, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3255, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC209 (pattern : Twelve) (guard : d3256 pattern = 1) : d211 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC207 pattern childGuard
    simpa only [d3256, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC208 pattern childGuard
    simpa only [d3256, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC210 (pattern : Twelve) (guard : d3257 pattern = 1) : d214 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d214, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC200 pattern childGuard
    simpa only [d3257, d214, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d214, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC209 pattern childGuard
    simpa only [d3257, d214, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC211 (pattern : Twelve) (guard : d3260 pattern = 1) : d215 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d215, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC209 pattern childGuard
    simpa only [d3260, d215, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d215, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC134 pattern childGuard
    simpa only [d3260, d215, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC212 (pattern : Twelve) (guard : d3261 pattern = 1) : d217 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d217, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC210 pattern childGuard
    simpa only [d3261, d217, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d217, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC211 pattern childGuard
    simpa only [d3261, d217, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC213 (pattern : Twelve) (guard : d3262 pattern = 1) : d218 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d218, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC190 pattern childGuard
    simpa only [d3262, d218, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d218, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC212 pattern childGuard
    simpa only [d3262, d218, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC214 (pattern : Twelve) (guard : d3265 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC215 (pattern : Twelve) (guard : d3266 pattern = 1) : d219 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d219, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC213 pattern childGuard
    simpa only [d3266, d219, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d219, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC214 pattern childGuard
    simpa only [d3266, d219, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC216 (pattern : Twelve) (guard : d3269 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC217 (pattern : Twelve) (guard : d3270 pattern = 1) : d220 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d220, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC215 pattern childGuard
    simpa only [d3270, d220, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d220, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC216 pattern childGuard
    simpa only [d3270, d220, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC218 (pattern : Twelve) (guard : d3273 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC219 (pattern : Twelve) (guard : d3274 pattern = 1) : d221 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d221, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC217 pattern childGuard
    simpa only [d3274, d221, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d221, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC218 pattern childGuard
    simpa only [d3274, d221, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC220 (pattern : Twelve) (guard : d3258 pattern = 1) : d222 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d222, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC52 pattern childGuard
    simpa only [d3258, d222, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d222, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC189 pattern childGuard
    simpa only [d3258, d222, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC221 (pattern : Twelve) (guard : d3261 pattern = 1) : d223 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d223, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC118 pattern childGuard
    simpa only [d3261, d223, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d223, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC211 pattern childGuard
    simpa only [d3261, d223, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC222 (pattern : Twelve) (guard : d3262 pattern = 1) : d228 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3258 pattern = 1 := by simpa only [d3262, d228, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC220 pattern childGuard
    simpa only [d3262, d228, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3262, d228, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC221 pattern childGuard
    simpa only [d3262, d228, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC223 (pattern : Twelve) (guard : d3265 pattern = 1) : d229 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range229 pattern).2
  change d229 pattern ≤ (0 : Int) + 6
  omega
theorem goalC224 (pattern : Twelve) (guard : d3266 pattern = 1) : d231 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3262 pattern = 1 := by simpa only [d3266, d231, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC222 pattern childGuard
    simpa only [d3266, d231, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3266, d231, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC223 pattern childGuard
    simpa only [d3266, d231, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC225 (pattern : Twelve) (guard : d3269 pattern = 1) : d232 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range232 pattern).2
  change d232 pattern ≤ (0 : Int) + 6
  omega
theorem goalC226 (pattern : Twelve) (guard : d3270 pattern = 1) : d233 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3266 pattern = 1 := by simpa only [d3270, d233, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC224 pattern childGuard
    simpa only [d3270, d233, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3270, d233, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC225 pattern childGuard
    simpa only [d3270, d233, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC227 (pattern : Twelve) (guard : d3273 pattern = 1) : d232 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range232 pattern).2
  change d232 pattern ≤ (0 : Int) + 6
  omega
theorem goalC228 (pattern : Twelve) (guard : d3274 pattern = 1) : d234 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3270 pattern = 1 := by simpa only [d3274, d234, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC226 pattern childGuard
    simpa only [d3274, d234, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3274, d234, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC227 pattern childGuard
    simpa only [d3274, d234, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC229 (pattern : Twelve) (guard : d3243 pattern = 1) : d235 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d3243, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC0 pattern childGuard
    simpa only [d3243, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3243, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC151 pattern childGuard
    simpa only [d3243, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC230 (pattern : Twelve) (guard : d3245 pattern = 1) : d236 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC4 pattern childGuard
    simpa only [d3245, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC155 pattern childGuard
    simpa only [d3245, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC231 (pattern : Twelve) (guard : d3246 pattern = 1) : d256 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3243 pattern = 1 := by simpa only [d3246, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC229 pattern childGuard
    simpa only [d3246, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3246, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC230 pattern childGuard
    simpa only [d3246, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC232 (pattern : Twelve) (guard : d3245 pattern = 1) : d237 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC2 pattern childGuard
    simpa only [d3245, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC155 pattern childGuard
    simpa only [d3245, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC233 (pattern : Twelve) (guard : d3248 pattern = 1) : d238 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC17 pattern childGuard
    simpa only [d3248, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC159 pattern childGuard
    simpa only [d3248, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC234 (pattern : Twelve) (guard : d3249 pattern = 1) : d257 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC232 pattern childGuard
    simpa only [d3249, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC233 pattern childGuard
    simpa only [d3249, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC235 (pattern : Twelve) (guard : d3250 pattern = 1) : d272 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3246 pattern = 1 := by simpa only [d3250, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC231 pattern childGuard
    simpa only [d3250, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3250, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC234 pattern childGuard
    simpa only [d3250, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC236 (pattern : Twelve) (guard : d3245 pattern = 1) : d239 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC25 pattern childGuard
    simpa only [d3245, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC167 pattern childGuard
    simpa only [d3245, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC237 (pattern : Twelve) (guard : d3248 pattern = 1) : d240 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC34 pattern childGuard
    simpa only [d3248, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC170 pattern childGuard
    simpa only [d3248, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC238 (pattern : Twelve) (guard : d3249 pattern = 1) : d258 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC236 pattern childGuard
    simpa only [d3249, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC237 pattern childGuard
    simpa only [d3249, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC239 (pattern : Twelve) (guard : d3251 pattern = 1) : d241 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC47 pattern childGuard
    simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3251, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC240 (pattern : Twelve) (guard : d3252 pattern = 1) : d259 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC237 pattern childGuard
    simpa only [d3252, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d3252, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC241 (pattern : Twelve) (guard : d3253 pattern = 1) : d273 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC238 pattern childGuard
    simpa only [d3253, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC240 pattern childGuard
    simpa only [d3253, d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC242 (pattern : Twelve) (guard : d3254 pattern = 1) : d284 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3250 pattern = 1 := by simpa only [d3254, d284, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC235 pattern childGuard
    simpa only [d3254, d284, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3254, d284, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC241 pattern childGuard
    simpa only [d3254, d284, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC243 (pattern : Twelve) (guard : d3245 pattern = 1) : d242 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC54 pattern childGuard
    simpa only [d3245, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC167 pattern childGuard
    simpa only [d3245, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC244 (pattern : Twelve) (guard : d3248 pattern = 1) : d243 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC59 pattern childGuard
    simpa only [d3248, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC170 pattern childGuard
    simpa only [d3248, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC245 (pattern : Twelve) (guard : d3249 pattern = 1) : d260 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC243 pattern childGuard
    simpa only [d3249, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC244 pattern childGuard
    simpa only [d3249, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC246 (pattern : Twelve) (guard : d3248 pattern = 1) : d244 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC56 pattern childGuard
    simpa only [d3248, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC170 pattern childGuard
    simpa only [d3248, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC247 (pattern : Twelve) (guard : d3252 pattern = 1) : d261 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC246 pattern childGuard
    simpa only [d3252, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d3252, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC248 (pattern : Twelve) (guard : d3253 pattern = 1) : d274 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC245 pattern childGuard
    simpa only [d3253, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC247 pattern childGuard
    simpa only [d3253, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC249 (pattern : Twelve) (guard : d3248 pattern = 1) : d245 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC69 pattern childGuard
    simpa only [d3248, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC182 pattern childGuard
    simpa only [d3248, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC250 (pattern : Twelve) (guard : d3251 pattern = 1) : d246 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC73 pattern childGuard
    simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3251, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC251 (pattern : Twelve) (guard : d3252 pattern = 1) : d262 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC249 pattern childGuard
    simpa only [d3252, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC250 pattern childGuard
    simpa only [d3252, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC252 (pattern : Twelve) (guard : d0 pattern = 1) : d241 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC253 (pattern : Twelve) (guard : d3255 pattern = 1) : d263 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC250 pattern childGuard
    simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC252 pattern childGuard
    simpa only [d3255, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC254 (pattern : Twelve) (guard : d3256 pattern = 1) : d275 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC251 pattern childGuard
    simpa only [d3256, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC253 pattern childGuard
    simpa only [d3256, d275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC255 (pattern : Twelve) (guard : d3257 pattern = 1) : d285 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d285, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC248 pattern childGuard
    simpa only [d3257, d285, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d285, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC254 pattern childGuard
    simpa only [d3257, d285, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC256 (pattern : Twelve) (guard : d3258 pattern = 1) : d293 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3254 pattern = 1 := by simpa only [d3258, d293, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC242 pattern childGuard
    simpa only [d3258, d293, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3258, d293, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC255 pattern childGuard
    simpa only [d3258, d293, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC257 (pattern : Twelve) (guard : d3245 pattern = 1) : d247 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3242 pattern = 1 := by simpa only [d3245, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC85 pattern childGuard
    simpa only [d3245, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3245, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC192 pattern childGuard
    simpa only [d3245, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC258 (pattern : Twelve) (guard : d3248 pattern = 1) : d248 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC87 pattern childGuard
    simpa only [d3248, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC194 pattern childGuard
    simpa only [d3248, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC259 (pattern : Twelve) (guard : d3249 pattern = 1) : d264 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC257 pattern childGuard
    simpa only [d3249, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC258 pattern childGuard
    simpa only [d3249, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
