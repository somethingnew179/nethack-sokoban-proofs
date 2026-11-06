/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons20
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c3360 (pattern : Ten) (guard : d350 pattern = 1) : d204 pattern ≤ (2 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d204, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3359 pattern childGuard
    simpa only [d204, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d204, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3346 pattern childGuard
    simpa only [d204, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3361 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d10 pattern := by
  change (8 : Int) ≤ (2 : Int) + 10
  decide
theorem c3362 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3361 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1970 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3363 (pattern : Ten) (guard : d0 pattern = 1) : d195 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3364 (pattern : Ten) (guard : d350 pattern = 1) : d195 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3362 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3363 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3365 (pattern : Ten) (guard : d350 pattern = 1) : d200 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3364 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3366 (pattern : Ten) (guard : d350 pattern = 1) : d205 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3365 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3367 (pattern : Ten) (guard : d350 pattern = 1) : d208 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d208, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3360 pattern childGuard
    simpa only [d208, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d208, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3366 pattern childGuard
    simpa only [d208, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3368 (pattern : Ten) (guard : d350 pattern = 1) : d212 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3367 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3353 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3369 (pattern : Ten) (guard : d350 pattern = 1) : d215 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3354 pattern childGuard
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3368 pattern childGuard
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3370 (pattern : Ten) (guard : d561 pattern = 1) : d298 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d561, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3327 pattern childGuard
    simpa only [d561, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d561, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3369 pattern childGuard
    simpa only [d561, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3371 (pattern : Ten) (guard : d0 pattern = 1) : d299 pattern ≤ (2 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3372 (pattern : Ten) (guard : d562 pattern = 1) : d300 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d561 pattern = 1 := by simpa only [d562, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3370 pattern childGuard
    simpa only [d562, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d562, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3371 pattern childGuard
    simpa only [d562, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3373 (pattern : Ten) (guard : d379 pattern = 1) : d207 pattern ≤ (1 : Int) + d207 pattern := by
  omega
theorem c3374 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (1 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3375 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d1 pattern := by
  change (2 : Int) ≤ (1 : Int) + 1
  decide
theorem c3376 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1737 pattern childGuard
    simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3375 pattern childGuard
    simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3377 (pattern : Ten) (guard : d379 pattern = 1) : d313 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d379, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3374 pattern childGuard
    simpa only [d379, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d379, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3376 pattern childGuard
    simpa only [d379, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3378 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (1 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3379 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d3 pattern := by
  change (4 : Int) ≤ (1 : Int) + 3
  decide
theorem c3380 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3379 pattern childGuard
    simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3381 (pattern : Ten) (guard : d379 pattern = 1) : d314 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d379, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3378 pattern childGuard
    simpa only [d379, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d379, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3380 pattern childGuard
    simpa only [d379, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3382 (pattern : Ten) (guard : d379 pattern = 1) : d317 pattern ≤ (1 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3377 pattern childGuard
    simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3381 pattern childGuard
    simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3383 (pattern : Ten) (guard : d0 pattern = 1) : d193 pattern ≤ (1 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3384 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (1 : Int) + d4 pattern := by
  change (5 : Int) ≤ (1 : Int) + 4
  decide
theorem c3385 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (1 : Int) + d5 pattern := by
  change (6 : Int) ≤ (1 : Int) + 5
  decide
theorem c3386 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (1 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3384 pattern childGuard
    simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3385 pattern childGuard
    simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3387 (pattern : Ten) (guard : d379 pattern = 1) : d315 pattern ≤ (1 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d379, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3383 pattern childGuard
    simpa only [d379, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d379, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3386 pattern childGuard
    simpa only [d379, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3388 (pattern : Ten) (guard : d379 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c3389 (pattern : Ten) (guard : d379 pattern = 1) : d318 pattern ≤ (1 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3387 pattern childGuard
    simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3390 (pattern : Ten) (guard : d379 pattern = 1) : d321 pattern ≤ (1 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3382 pattern childGuard
    simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3389 pattern childGuard
    simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3391 (pattern : Ten) (guard : d0 pattern = 1) : d194 pattern ≤ (1 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3392 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d6 pattern := by
  change (7 : Int) ≤ (1 : Int) + 6
  decide
theorem c3393 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d7 pattern := by
  change (8 : Int) ≤ (1 : Int) + 7
  decide
theorem c3394 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (1 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3392 pattern childGuard
    simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3393 pattern childGuard
    simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3395 (pattern : Ten) (guard : d379 pattern = 1) : d316 pattern ≤ (1 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d379, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3391 pattern childGuard
    simpa only [d379, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d379, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3394 pattern childGuard
    simpa only [d379, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3396 (pattern : Ten) (guard : d379 pattern = 1) : d319 pattern ≤ (1 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3395 pattern childGuard
    simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3397 (pattern : Ten) (guard : d379 pattern = 1) : d322 pattern ≤ (1 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3396 pattern childGuard
    simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3398 (pattern : Ten) (guard : d379 pattern = 1) : d324 pattern ≤ (1 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3390 pattern childGuard
    simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3397 pattern childGuard
    simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3399 (pattern : Ten) (guard : d379 pattern = 1) : d332 pattern ≤ (1 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3373 pattern childGuard
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3398 pattern childGuard
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3400 (pattern : Ten) (guard : d379 pattern = 1) : d333 pattern ≤ (1 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3398 pattern childGuard
    simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d333, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3401 (pattern : Ten) (guard : d379 pattern = 1) : d320 pattern ≤ (1 : Int) + d199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3381 pattern childGuard
    simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3387 pattern childGuard
    simpa only [d320, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3402 (pattern : Ten) (guard : d379 pattern = 1) : d323 pattern ≤ (1 : Int) + d204 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3401 pattern childGuard
    simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3396 pattern childGuard
    simpa only [d323, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3403 (pattern : Ten) (guard : d0 pattern = 1) : d195 pattern ≤ (1 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3404 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d8 pattern := by
  change (9 : Int) ≤ (1 : Int) + 8
  decide
theorem c3405 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3404 pattern childGuard
    simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1713 pattern childGuard
    simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3406 (pattern : Ten) (guard : d379 pattern = 1) : d196 pattern ≤ (1 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d379, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3403 pattern childGuard
    simpa only [d379, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d379, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3405 pattern childGuard
    simpa only [d379, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3407 (pattern : Ten) (guard : d379 pattern = 1) : d201 pattern ≤ (1 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3406 pattern childGuard
    simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3408 (pattern : Ten) (guard : d379 pattern = 1) : d206 pattern ≤ (1 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3407 pattern childGuard
    simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3409 (pattern : Ten) (guard : d379 pattern = 1) : d325 pattern ≤ (1 : Int) + d208 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3402 pattern childGuard
    simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3408 pattern childGuard
    simpa only [d325, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3410 (pattern : Ten) (guard : d379 pattern = 1) : d334 pattern ≤ (1 : Int) + d212 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3409 pattern childGuard
    simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d334, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3411 (pattern : Ten) (guard : d379 pattern = 1) : d336 pattern ≤ (1 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3400 pattern childGuard
    simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3410 pattern childGuard
    simpa only [d336, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3412 (pattern : Ten) (guard : d379 pattern = 1) : d338 pattern ≤ (1 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d338, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3399 pattern childGuard
    simpa only [d338, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d338, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3411 pattern childGuard
    simpa only [d338, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3413 (pattern : Ten) (guard : d379 pattern = 1) : d209 pattern ≤ (1 : Int) + d209 pattern := by
  omega
theorem c3414 (pattern : Ten) (guard : d379 pattern = 1) : d210 pattern ≤ (1 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3408 pattern childGuard
    simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3415 (pattern : Ten) (guard : d379 pattern = 1) : d213 pattern ≤ (1 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3413 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3414 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3416 (pattern : Ten) (guard : d379 pattern = 1) : d335 pattern ≤ (1 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3414 pattern childGuard
    simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d335, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3417 (pattern : Ten) (guard : d379 pattern = 1) : d337 pattern ≤ (1 : Int) + d217 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3416 pattern childGuard
    simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3388 pattern childGuard
    simpa only [d337, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3418 (pattern : Ten) (guard : d379 pattern = 1) : d339 pattern ≤ (1 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3415 pattern childGuard
    simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3417 pattern childGuard
    simpa only [d339, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3419 (pattern : Ten) (guard : d379 pattern = 1) : d340 pattern ≤ (1 : Int) + d566 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d340, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3412 pattern childGuard
    simpa only [d340, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d340, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3418 pattern childGuard
    simpa only [d340, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3420 (pattern : Ten) (guard : d379 pattern = 1) : d218 pattern ≤ (1 : Int) + d218 pattern := by
  omega
theorem c3421 (pattern : Ten) (guard : d379 pattern = 1) : d216 pattern ≤ (1 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3413 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3415 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3422 (pattern : Ten) (guard : d379 pattern = 1) : d217 pattern ≤ (1 : Int) + d217 pattern := by
  omega
theorem c3423 (pattern : Ten) (guard : d379 pattern = 1) : d219 pattern ≤ (1 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3421 pattern childGuard
    simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3422 pattern childGuard
    simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3424 (pattern : Ten) (guard : d379 pattern = 1) : d220 pattern ≤ (1 : Int) + d566 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d379 pattern = 1 := by simpa only [d220, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3420 pattern childGuard
    simpa only [d220, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d379 pattern = 1 := by simpa only [d220, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3423 pattern childGuard
    simpa only [d220, d566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3425 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (2 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3426 (pattern : Ten) (guard : d567 pattern = 1) : d160 pattern ≤ (2 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d567, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3425 pattern childGuard
    simpa only [d567, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d567, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2387 pattern childGuard
    simpa only [d567, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3427 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (2 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3428 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (2 : Int) + d44 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2379 pattern childGuard
    simpa only [d157, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2381 pattern childGuard
    simpa only [d157, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3429 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (2 : Int) + d50 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3428 pattern childGuard
    simpa only [d158, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2385 pattern childGuard
    simpa only [d158, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3430 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d8 pattern := by
  change (10 : Int) ≤ (2 : Int) + 8
  decide
theorem c3431 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3430 pattern childGuard
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3432 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3431 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3433 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3429 pattern childGuard
    simpa only [d159, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3432 pattern childGuard
    simpa only [d159, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3434 (pattern : Ten) (guard : d567 pattern = 1) : d161 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d567, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3427 pattern childGuard
    simpa only [d567, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d567, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3433 pattern childGuard
    simpa only [d567, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3435 (pattern : Ten) (guard : d567 pattern = 1) : d165 pattern ≤ (2 : Int) + d152 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d567 pattern = 1 := by simpa only [d165, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3426 pattern childGuard
    simpa only [d165, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d567 pattern = 1 := by simpa only [d165, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3434 pattern childGuard
    simpa only [d165, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3436 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (2 : Int) + d152 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3437 (pattern : Ten) (guard : d568 pattern = 1) : d168 pattern ≤ (2 : Int) + d152 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d567 pattern = 1 := by simpa only [d568, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3435 pattern childGuard
    simpa only [d568, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d568, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3436 pattern childGuard
    simpa only [d568, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3438 (pattern : Ten) (guard : d567 pattern = 1) : d164 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d567, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3100 pattern childGuard
    simpa only [d567, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d567, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2402 pattern childGuard
    simpa only [d567, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3439 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (2 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3440 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2433 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3441 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3440 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3442 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d41 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3443 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3441 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3442 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3444 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3443 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3445 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d53 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3444 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3446 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3445 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3447 (pattern : Ten) (guard : d567 pattern = 1) : d60 pattern ≤ (2 : Int) + d57 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d567, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3439 pattern childGuard
    simpa only [d567, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d567, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3446 pattern childGuard
    simpa only [d567, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3448 (pattern : Ten) (guard : d567 pattern = 1) : d167 pattern ≤ (2 : Int) + d153 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d567 pattern = 1 := by simpa only [d167, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3438 pattern childGuard
    simpa only [d167, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d567 pattern = 1 := by simpa only [d167, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3447 pattern childGuard
    simpa only [d167, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3449 (pattern : Ten) (guard : d0 pattern = 1) : d63 pattern ≤ (2 : Int) + d153 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3450 (pattern : Ten) (guard : d568 pattern = 1) : d169 pattern ≤ (2 : Int) + d153 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d567 pattern = 1 := by simpa only [d568, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3448 pattern childGuard
    simpa only [d568, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d568, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3449 pattern childGuard
    simpa only [d568, d169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3451 (pattern : Ten) (guard : d568 pattern = 1) : d170 pattern ≤ (2 : Int) + d569 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d568 pattern = 1 := by simpa only [d170, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3437 pattern childGuard
    simpa only [d170, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d568 pattern = 1 := by simpa only [d170, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3450 pattern childGuard
    simpa only [d170, d569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3452 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (2 : Int) + d324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3453 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (2 : Int) + d309 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2410 pattern childGuard
    simpa only [d310, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2412 pattern childGuard
    simpa only [d310, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3454 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (2 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2411 pattern childGuard
    simpa only [d314, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3453 pattern childGuard
    simpa only [d314, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3455 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (2 : Int) + d310 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2413 pattern childGuard
    simpa only [d311, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2416 pattern childGuard
    simpa only [d311, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3456 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (2 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2414 pattern childGuard
    simpa only [d315, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3455 pattern childGuard
    simpa only [d315, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3457 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (2 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3454 pattern childGuard
    simpa only [d320, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3456 pattern childGuard
    simpa only [d320, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3458 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (2 : Int) + d311 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2417 pattern childGuard
    simpa only [d312, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2421 pattern childGuard
    simpa only [d312, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3459 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (2 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2418 pattern childGuard
    simpa only [d316, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3458 pattern childGuard
    simpa only [d316, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3460 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (2 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3459 pattern childGuard
    simpa only [d319, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d319, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3461 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (2 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3457 pattern childGuard
    simpa only [d323, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3460 pattern childGuard
    simpa only [d323, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3462 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d312 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2394 pattern childGuard
    simpa only [d11, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d11, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3463 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (2 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2422 pattern childGuard
    simpa only [d196, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3462 pattern childGuard
    simpa only [d196, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3464 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (2 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3463 pattern childGuard
    simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3465 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (2 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3464 pattern childGuard
    simpa only [d206, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d206, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3466 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (2 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3461 pattern childGuard
    simpa only [d325, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3465 pattern childGuard
    simpa only [d325, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3467 (pattern : Ten) (guard : d402 pattern = 1) : d344 pattern ≤ (2 : Int) + d324 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d402, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3452 pattern childGuard
    simpa only [d402, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d402, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3466 pattern childGuard
    simpa only [d402, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3468 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (2 : Int) + d325 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3469 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (2 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3456 pattern childGuard
    simpa only [d341, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3459 pattern childGuard
    simpa only [d341, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3470 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (2 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3469 pattern childGuard
    simpa only [d342, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3464 pattern childGuard
    simpa only [d342, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3471 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2442 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2848 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3472 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3471 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3473 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3472 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3474 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (2 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3470 pattern childGuard
    simpa only [d343, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3473 pattern childGuard
    simpa only [d343, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3475 (pattern : Ten) (guard : d402 pattern = 1) : d345 pattern ≤ (2 : Int) + d325 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d402, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d402, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d402, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3474 pattern childGuard
    simpa only [d402, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3476 (pattern : Ten) (guard : d402 pattern = 1) : d346 pattern ≤ (2 : Int) + d327 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d402 pattern = 1 := by simpa only [d346, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3467 pattern childGuard
    simpa only [d346, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d402 pattern = 1 := by simpa only [d346, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3475 pattern childGuard
    simpa only [d346, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3477 (pattern : Ten) (guard : d0 pattern = 1) : d336 pattern ≤ (2 : Int) + d327 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3478 (pattern : Ten) (guard : d570 pattern = 1) : d347 pattern ≤ (2 : Int) + d327 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d402 pattern = 1 := by simpa only [d570, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3476 pattern childGuard
    simpa only [d570, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d570, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3477 pattern childGuard
    simpa only [d570, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3479 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (2 : Int) + d210 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3480 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3473 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3481 (pattern : Ten) (guard : d402 pattern = 1) : d214 pattern ≤ (2 : Int) + d210 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3479 pattern childGuard
    simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3480 pattern childGuard
    simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3482 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3483 (pattern : Ten) (guard : d402 pattern = 1) : d214 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3482 pattern childGuard
    simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d402, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3484 (pattern : Ten) (guard : d402 pattern = 1) : d214 pattern ≤ (2 : Int) + d328 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d402 pattern = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3481 pattern childGuard
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d402 pattern = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3483 pattern childGuard
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3485 (pattern : Ten) (guard : d0 pattern = 1) : d337 pattern ≤ (2 : Int) + d328 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3486 (pattern : Ten) (guard : d570 pattern = 1) : d348 pattern ≤ (2 : Int) + d328 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d402 pattern = 1 := by simpa only [d570, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3484 pattern childGuard
    simpa only [d570, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d570, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3485 pattern childGuard
    simpa only [d570, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3487 (pattern : Ten) (guard : d570 pattern = 1) : d349 pattern ≤ (2 : Int) + d571 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d570 pattern = 1 := by simpa only [d349, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3478 pattern childGuard
    simpa only [d349, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d570 pattern = 1 := by simpa only [d349, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3486 pattern childGuard
    simpa only [d349, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3488 (pattern : Ten) (guard : d567 pattern = 1) : d54 pattern ≤ (0 : Int) + d54 pattern := by
  omega
theorem c3489 (pattern : Ten) (guard : d568 pattern = 1) : d134 pattern ≤ (0 : Int) + d572 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d567 pattern = 1 := by simpa only [d568, d134, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3488 pattern childGuard
    simpa only [d568, d134, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d568, d134, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c917 pattern childGuard
    simpa only [d568, d134, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3490 (pattern : Ten) (guard : d567 pattern = 1) : d56 pattern ≤ (0 : Int) + d56 pattern := by
  omega
theorem c3491 (pattern : Ten) (guard : d568 pattern = 1) : d56 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d567 pattern = 1 := by simpa only [d568, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3490 pattern childGuard
    simpa only [d568, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d568, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c920 pattern childGuard
    simpa only [d568, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3492 (pattern : Ten) (guard : d568 pattern = 1) : d135 pattern ≤ (0 : Int) + d573 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d568 pattern = 1 := by simpa only [d135, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3489 pattern childGuard
    simpa only [d135, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d568 pattern = 1 := by simpa only [d135, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3491 pattern childGuard
    simpa only [d135, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3493 (pattern : Ten) (guard : d402 pattern = 1) : d207 pattern ≤ (0 : Int) + d207 pattern := by
  omega
theorem c3494 (pattern : Ten) (guard : d570 pattern = 1) : d290 pattern ≤ (0 : Int) + d574 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d402 pattern = 1 := by simpa only [d570, d290, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3493 pattern childGuard
    simpa only [d570, d290, d574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d570, d290, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c923 pattern childGuard
    simpa only [d570, d290, d574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3495 (pattern : Ten) (guard : d402 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c3496 (pattern : Ten) (guard : d570 pattern = 1) : d209 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d402 pattern = 1 := by simpa only [d570, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3495 pattern childGuard
    simpa only [d570, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d570, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c926 pattern childGuard
    simpa only [d570, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3497 (pattern : Ten) (guard : d570 pattern = 1) : d291 pattern ≤ (0 : Int) + d575 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d570 pattern = 1 := by simpa only [d291, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3494 pattern childGuard
    simpa only [d291, d575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d570 pattern = 1 := by simpa only [d291, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3496 pattern childGuard
    simpa only [d291, d575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3498 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem c3499 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d4 pattern := by
  change (2 : Int) ≤ (2 : Int) + 4
  decide
theorem c3500 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (2 : Int) + d44 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3498 pattern childGuard
    simpa only [d15, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3499 pattern childGuard
    simpa only [d15, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3501 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (2 : Int) + d6 pattern := by
  change (4 : Int) ≤ (2 : Int) + 6
  decide
theorem c3502 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3501 pattern childGuard
    simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3503 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (2 : Int) + d50 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d48, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3502 pattern childGuard
    simpa only [d48, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3504 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (2 : Int) + d8 pattern := by
  change (6 : Int) ≤ (2 : Int) + 8
  decide
theorem c3505 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3504 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3506 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (2 : Int) + d51 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3505 pattern childGuard
    simpa only [d49, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d49, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3507 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3503 pattern childGuard
    simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3506 pattern childGuard
    simpa only [d54, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3508 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (2 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3509 (pattern : Ten) (guard : d395 pattern = 1) : d160 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3507 pattern childGuard
    simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3508 pattern childGuard
    simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3510 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (2 : Int) + d4 pattern := by
  change (0 : Int) ≤ (2 : Int) + 4
  decide
theorem c3511 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d6 pattern := by
  change (2 : Int) ≤ (2 : Int) + 6
  decide
theorem c3512 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (2 : Int) + d157 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3510 pattern childGuard
    simpa only [d15, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3511 pattern childGuard
    simpa only [d15, d157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3513 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (2 : Int) + d8 pattern := by
  change (4 : Int) ≤ (2 : Int) + 8
  decide
theorem c3514 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3513 pattern childGuard
    simpa only [d42, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d42, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3515 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (2 : Int) + d158 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3512 pattern childGuard
    simpa only [d48, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3514 pattern childGuard
    simpa only [d48, d158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3516 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (2 : Int) + d159 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3515 pattern childGuard
    simpa only [d54, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3300 pattern childGuard
    simpa only [d54, d159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3517 (pattern : Ten) (guard : d0 pattern = 1) : d159 pattern ≤ (2 : Int) + d159 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3518 (pattern : Ten) (guard : d395 pattern = 1) : d161 pattern ≤ (2 : Int) + d159 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3516 pattern childGuard
    simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3517 pattern childGuard
    simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3519 (pattern : Ten) (guard : d395 pattern = 1) : d165 pattern ≤ (2 : Int) + d576 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3509 pattern childGuard
    simpa only [d165, d576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3518 pattern childGuard
    simpa only [d165, d576, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
