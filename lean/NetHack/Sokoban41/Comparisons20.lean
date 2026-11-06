/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons19
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c3200 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (9 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3198 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3199 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3201 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d2 pattern := by
  change (4 : Int) ≤ (9 : Int) + 2
  decide
theorem c3202 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d3 pattern := by
  change (4 : Int) ≤ (9 : Int) + 3
  decide
theorem c3203 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3201 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3202 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3204 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (9 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3205 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (9 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3203 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3204 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3206 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (9 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3200 pattern childGuard
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3205 pattern childGuard
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3207 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d4 pattern := by
  change (6 : Int) ≤ (9 : Int) + 4
  decide
theorem c3208 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d5 pattern := by
  change (6 : Int) ≤ (9 : Int) + 5
  decide
theorem c3209 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3207 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3208 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3210 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (9 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3211 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (9 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3209 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3210 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3212 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (9 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3211 pattern childGuard
    simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3213 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (9 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3206 pattern childGuard
    simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3212 pattern childGuard
    simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3214 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (9 : Int) + d6 pattern := by
  change (8 : Int) ≤ (9 : Int) + 6
  decide
theorem c3215 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (9 : Int) + d7 pattern := by
  change (8 : Int) ≤ (9 : Int) + 7
  decide
theorem c3216 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (9 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3214 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3215 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3217 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (9 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3218 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (9 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3216 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3217 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3219 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (9 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3218 pattern childGuard
    simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3220 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (9 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3219 pattern childGuard
    simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3221 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3213 pattern childGuard
    simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3220 pattern childGuard
    simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3222 (pattern : Ten) (guard : d350 pattern = 1) : d59 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3221 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3194 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3223 (pattern : Ten) (guard : d350 pattern = 1) : d62 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3195 pattern childGuard
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3222 pattern childGuard
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3224 (pattern : Ten) (guard : d561 pattern = 1) : d64 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3141 pattern childGuard
    simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3223 pattern childGuard
    simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3225 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (9 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3226 (pattern : Ten) (guard : d562 pattern = 1) : d133 pattern ≤ (9 : Int) + d560 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d561 pattern = 1 := by simpa only [d562, d133, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3224 pattern childGuard
    simpa only [d562, d133, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d562, d133, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3225 pattern childGuard
    simpa only [d562, d133, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3227 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3228 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) ≤ (9 : Int) + 10
  decide
theorem c3229 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (9 : Int) + d10 pattern := by
  change (1 : Int) ≤ (9 : Int) + 10
  decide
theorem c3230 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3228 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3229 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3231 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3232 (pattern : Ten) (guard : d350 pattern = 1) : d171 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3230 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3231 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3233 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d10 pattern := by
  change (2 : Int) ≤ (9 : Int) + 10
  decide
theorem c3234 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (9 : Int) + d10 pattern := by
  change (3 : Int) ≤ (9 : Int) + 10
  decide
theorem c3235 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3233 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3234 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3236 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3237 (pattern : Ten) (guard : d350 pattern = 1) : d172 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3235 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3236 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3238 (pattern : Ten) (guard : d350 pattern = 1) : d174 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3232 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3237 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3239 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d10 pattern := by
  change (4 : Int) ≤ (9 : Int) + 10
  decide
theorem c3240 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (9 : Int) + d10 pattern := by
  change (5 : Int) ≤ (9 : Int) + 10
  decide
theorem c3241 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3239 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3240 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3242 (pattern : Ten) (guard : d0 pattern = 1) : d193 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3243 (pattern : Ten) (guard : d350 pattern = 1) : d193 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3241 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3242 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3244 (pattern : Ten) (guard : d350 pattern = 1) : d197 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3243 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3245 (pattern : Ten) (guard : d350 pattern = 1) : d202 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3238 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3244 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3246 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d10 pattern := by
  change (6 : Int) ≤ (9 : Int) + 10
  decide
theorem c3247 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (9 : Int) + d10 pattern := by
  change (7 : Int) ≤ (9 : Int) + 10
  decide
theorem c3248 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3246 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3247 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3249 (pattern : Ten) (guard : d0 pattern = 1) : d194 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3250 (pattern : Ten) (guard : d350 pattern = 1) : d194 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3248 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3249 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3251 (pattern : Ten) (guard : d350 pattern = 1) : d198 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3250 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3252 (pattern : Ten) (guard : d350 pattern = 1) : d203 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3251 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3253 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3245 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3252 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3254 (pattern : Ten) (guard : d350 pattern = 1) : d211 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3253 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3255 (pattern : Ten) (guard : d350 pattern = 1) : d199 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3237 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3243 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3256 (pattern : Ten) (guard : d350 pattern = 1) : d204 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3255 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3251 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3257 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (9 : Int) + d10 pattern := by
  change (8 : Int) ≤ (9 : Int) + 10
  decide
theorem c3258 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (9 : Int) + d10 pattern := by
  change (9 : Int) ≤ (9 : Int) + 10
  decide
theorem c3259 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3257 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3258 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3260 (pattern : Ten) (guard : d0 pattern = 1) : d195 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3261 (pattern : Ten) (guard : d350 pattern = 1) : d195 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3259 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3260 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3262 (pattern : Ten) (guard : d350 pattern = 1) : d200 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3261 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3263 (pattern : Ten) (guard : d350 pattern = 1) : d205 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3262 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3264 (pattern : Ten) (guard : d350 pattern = 1) : d208 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3263 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3265 (pattern : Ten) (guard : d350 pattern = 1) : d212 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3264 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3266 (pattern : Ten) (guard : d350 pattern = 1) : d215 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3254 pattern childGuard
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3265 pattern childGuard
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3267 (pattern : Ten) (guard : d561 pattern = 1) : d218 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d561, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3227 pattern childGuard
    simpa only [d561, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d561, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3266 pattern childGuard
    simpa only [d561, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3268 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (9 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3269 (pattern : Ten) (guard : d562 pattern = 1) : d289 pattern ≤ (9 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d561 pattern = 1 := by simpa only [d562, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3267 pattern childGuard
    simpa only [d562, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d562, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3268 pattern childGuard
    simpa only [d562, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3270 (pattern : Ten) (guard : d0 pattern = 1) : d82 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3271 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3272 (pattern : Ten) (guard : d554 pattern = 1) : d58 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1000 pattern childGuard
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3271 pattern childGuard
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3273 (pattern : Ten) (guard : d555 pattern = 1) : d83 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d555, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3270 pattern childGuard
    simpa only [d555, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d554 pattern = 1 := by simpa only [d555, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3272 pattern childGuard
    simpa only [d555, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3274 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3275 (pattern : Ten) (guard : d554 pattern = 1) : d60 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c282 pattern childGuard
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3276 (pattern : Ten) (guard : d555 pattern = 1) : d84 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d555, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3274 pattern childGuard
    simpa only [d555, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d554 pattern = 1 := by simpa only [d555, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d555, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3277 (pattern : Ten) (guard : d555 pattern = 1) : d85 pattern ≤ (0 : Int) + d556 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d555 pattern = 1 := by simpa only [d85, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3273 pattern childGuard
    simpa only [d85, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d555 pattern = 1 := by simpa only [d85, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3276 pattern childGuard
    simpa only [d85, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3278 (pattern : Ten) (guard : d0 pattern = 1) : d235 pattern ≤ (0 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3279 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3280 (pattern : Ten) (guard : d558 pattern = 1) : d211 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1139 pattern childGuard
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3279 pattern childGuard
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3281 (pattern : Ten) (guard : d559 pattern = 1) : d236 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d559, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3278 pattern childGuard
    simpa only [d559, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d558 pattern = 1 := by simpa only [d559, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3280 pattern childGuard
    simpa only [d559, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3282 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3283 (pattern : Ten) (guard : d558 pattern = 1) : d214 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1314 pattern childGuard
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c288 pattern childGuard
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3284 (pattern : Ten) (guard : d559 pattern = 1) : d237 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d559, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3282 pattern childGuard
    simpa only [d559, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d558 pattern = 1 := by simpa only [d559, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3283 pattern childGuard
    simpa only [d559, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3285 (pattern : Ten) (guard : d559 pattern = 1) : d238 pattern ≤ (0 : Int) + d560 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d559 pattern = 1 := by simpa only [d238, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3281 pattern childGuard
    simpa only [d238, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d559 pattern = 1 := by simpa only [d238, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3284 pattern childGuard
    simpa only [d238, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3286 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (2 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3287 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d7 pattern := by
  change (0 : Int) ≤ (2 : Int) + 7
  decide
theorem c3288 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d8 pattern := by
  change (0 : Int) ≤ (2 : Int) + 8
  decide
theorem c3289 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3287 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3290 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3289 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3291 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3292 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3290 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3291 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3293 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d10 pattern := by
  change (2 : Int) ≤ (2 : Int) + 10
  decide
theorem c3294 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3292 pattern childGuard
    simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3293 pattern childGuard
    simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3295 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (2 : Int) + d10 pattern := by
  change (4 : Int) ≤ (2 : Int) + 10
  decide
theorem c3296 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3297 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (2 : Int) + d52 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3294 pattern childGuard
    simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3296 pattern childGuard
    simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3298 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (2 : Int) + d10 pattern := by
  change (6 : Int) ≤ (2 : Int) + 10
  decide
theorem c3299 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3300 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3299 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3301 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3297 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3300 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3302 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2394 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2432 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3303 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d11, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d11, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3304 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (2 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3305 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3303 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3304 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3306 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3305 pattern childGuard
    simpa only [d14, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d14, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3307 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (2 : Int) + d52 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3306 pattern childGuard
    simpa only [d20, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d20, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3308 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3307 pattern childGuard
    simpa only [d27, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d27, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3309 (pattern : Ten) (guard : d350 pattern = 1) : d58 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3301 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3308 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3310 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d7 pattern := by
  change (2 : Int) ≤ (2 : Int) + 7
  decide
theorem c3311 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d8 pattern := by
  change (2 : Int) ≤ (2 : Int) + 8
  decide
theorem c3312 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3310 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3313 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3312 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3314 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3315 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3313 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3314 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3316 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3315 pattern childGuard
    simpa only [d44, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3295 pattern childGuard
    simpa only [d44, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3317 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (2 : Int) + d52 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3316 pattern childGuard
    simpa only [d50, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3299 pattern childGuard
    simpa only [d50, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3318 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (2 : Int) + d10 pattern := by
  change (8 : Int) ≤ (2 : Int) + 10
  decide
theorem c3319 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3318 pattern childGuard
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3320 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3319 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3321 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3317 pattern childGuard
    simpa only [d55, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3320 pattern childGuard
    simpa only [d55, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3322 (pattern : Ten) (guard : d350 pattern = 1) : d59 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3321 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3308 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3323 (pattern : Ten) (guard : d350 pattern = 1) : d62 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3309 pattern childGuard
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3322 pattern childGuard
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3324 (pattern : Ten) (guard : d561 pattern = 1) : d64 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3286 pattern childGuard
    simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3323 pattern childGuard
    simpa only [d561, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3325 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (2 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3326 (pattern : Ten) (guard : d562 pattern = 1) : d66 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d561 pattern = 1 := by simpa only [d562, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3324 pattern childGuard
    simpa only [d562, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d562, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3325 pattern childGuard
    simpa only [d562, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3327 (pattern : Ten) (guard : d0 pattern = 1) : d297 pattern ≤ (2 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3328 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d9 pattern := by
  change (1 : Int) ≤ (2 : Int) + 9
  decide
theorem c3329 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3288 pattern childGuard
    simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3328 pattern childGuard
    simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3330 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (2 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3331 (pattern : Ten) (guard : d350 pattern = 1) : d171 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3329 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3330 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3332 (pattern : Ten) (guard : d350 pattern = 1) : d172 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2013 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3333 (pattern : Ten) (guard : d350 pattern = 1) : d174 pattern ≤ (2 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3331 pattern childGuard
    simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3332 pattern childGuard
    simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3334 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d10 pattern := by
  change (4 : Int) ≤ (2 : Int) + 10
  decide
theorem c3335 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d10 pattern := by
  change (5 : Int) ≤ (2 : Int) + 10
  decide
theorem c3336 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3334 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3335 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3337 (pattern : Ten) (guard : d0 pattern = 1) : d193 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3338 (pattern : Ten) (guard : d350 pattern = 1) : d193 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3336 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3337 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3339 (pattern : Ten) (guard : d350 pattern = 1) : d197 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3338 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3340 (pattern : Ten) (guard : d350 pattern = 1) : d202 pattern ≤ (2 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3333 pattern childGuard
    simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3339 pattern childGuard
    simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3341 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d10 pattern := by
  change (6 : Int) ≤ (2 : Int) + 10
  decide
theorem c3342 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d10 pattern := by
  change (7 : Int) ≤ (2 : Int) + 10
  decide
theorem c3343 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3341 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3342 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3344 (pattern : Ten) (guard : d0 pattern = 1) : d194 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3345 (pattern : Ten) (guard : d350 pattern = 1) : d194 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3343 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3344 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3346 (pattern : Ten) (guard : d350 pattern = 1) : d198 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3345 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3347 (pattern : Ten) (guard : d350 pattern = 1) : d203 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3348 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3340 pattern childGuard
    simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3347 pattern childGuard
    simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3349 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3350 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2442 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3349 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3351 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3350 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3352 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3351 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3353 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3352 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3354 (pattern : Ten) (guard : d350 pattern = 1) : d211 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3348 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3353 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3355 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d9 pattern := by
  change (3 : Int) ≤ (2 : Int) + 9
  decide
theorem c3356 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3311 pattern childGuard
    simpa only [d172, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3355 pattern childGuard
    simpa only [d172, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3357 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (2 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3358 (pattern : Ten) (guard : d350 pattern = 1) : d172 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3356 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3357 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3359 (pattern : Ten) (guard : d350 pattern = 1) : d199 pattern ≤ (2 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d199, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3358 pattern childGuard
    simpa only [d199, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d199, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3338 pattern childGuard
    simpa only [d199, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
