/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3360 (p : Pattern) (guard : d4302 p = 1) : d647 p ≤ (0 : Int) + d943 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d647, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3359 p hg
    simpa only [d4302, d647, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d647, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d647, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3361 (p : Pattern) (guard : d4302 p = 1) : d648 p ≤ (0 : Int) + d944 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d648, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3348 p hg
    simpa only [d648, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d648, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3360 p hg
    simpa only [d648, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3362 (p : Pattern) (guard : d4302 p = 1) : d649 p ≤ (0 : Int) + d945 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d649, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3341 p hg
    simpa only [d649, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d649, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3361 p hg
    simpa only [d649, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3363 (p : Pattern) (guard : d4302 p = 1) : d650 p ≤ (0 : Int) + d946 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d650, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d650, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d650, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3362 p hg
    simpa only [d650, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3364 (p : Pattern) (guard : d4302 p = 1) : d651 p ≤ (0 : Int) + d947 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d651, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3326 p hg
    simpa only [d651, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d651, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3363 p hg
    simpa only [d651, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3365 (p : Pattern) (guard : d4302 p = 1) : d652 p ≤ (0 : Int) + d948 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d652, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3309 p hg
    simpa only [d652, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d652, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3364 p hg
    simpa only [d652, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3366 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d77 p := by
  omega
theorem compare3367 (p : Pattern) (guard : d4203 p = 1) : d517 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2459 p hg
    simpa only [d4203, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3368 (p : Pattern) (guard : d0 p = 1) : d530 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3369 (p : Pattern) (guard : d4117 p = 1) : d531 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d531, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d531, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d531, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3368 p hg
    simpa only [d4117, d531, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3370 (p : Pattern) (guard : d0 p = 1) : d541 p ≤ (0 : Int) + d85 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3371 (p : Pattern) (guard : d4117 p = 1) : d542 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d542, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d542, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d542, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3370 p hg
    simpa only [d4117, d542, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3372 (p : Pattern) (guard : d4117 p = 1) : d543 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d543, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d543, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d543, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3371 p hg
    simpa only [d543, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3373 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d96 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3374 (p : Pattern) (guard : d4203 p = 1) : d544 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d544, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3372 p hg
    simpa only [d4203, d544, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d544, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3373 p hg
    simpa only [d4203, d544, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3375 (p : Pattern) (guard : d4203 p = 1) : d545 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3367 p hg
    simpa only [d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3374 p hg
    simpa only [d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3376 (p : Pattern) (guard : d4203 p = 1) : d546 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d4203, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3377 (p : Pattern) (guard : d4203 p = 1) : d547 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d547, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3372 p hg
    simpa only [d4203, d547, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d547, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d547, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3378 (p : Pattern) (guard : d4203 p = 1) : d548 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d548, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3376 p hg
    simpa only [d548, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d548, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3377 p hg
    simpa only [d548, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3379 (p : Pattern) (guard : d4203 p = 1) : d549 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d549, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3375 p hg
    simpa only [d549, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d549, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3378 p hg
    simpa only [d549, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3380 (p : Pattern) (guard : d4203 p = 1) : d550 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2468 p hg
    simpa only [d4203, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3381 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d96 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3382 (p : Pattern) (guard : d4203 p = 1) : d551 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d551, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3372 p hg
    simpa only [d4203, d551, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d551, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3381 p hg
    simpa only [d4203, d551, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3383 (p : Pattern) (guard : d4203 p = 1) : d552 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3380 p hg
    simpa only [d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3382 p hg
    simpa only [d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3384 (p : Pattern) (guard : d4203 p = 1) : d553 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2472 p hg
    simpa only [d4203, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3385 (p : Pattern) (guard : d4203 p = 1) : d554 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d554, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3384 p hg
    simpa only [d554, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d554, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3377 p hg
    simpa only [d554, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3386 (p : Pattern) (guard : d4203 p = 1) : d555 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d555, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d555, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d555, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3385 p hg
    simpa only [d555, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3387 (p : Pattern) (guard : d4203 p = 1) : d556 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3386 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3388 (p : Pattern) (guard : d4117 p = 1) : d147 p ≤ (0 : Int) + d147 p := by
  omega
theorem compare3389 (p : Pattern) (guard : d4203 p = 1) : d557 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d4203, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2478 p hg
    simpa only [d4203, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3390 (p : Pattern) (guard : d0 p = 1) : d568 p ≤ (0 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3391 (p : Pattern) (guard : d4117 p = 1) : d569 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d569, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d569, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d569, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3390 p hg
    simpa only [d4117, d569, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3392 (p : Pattern) (guard : d0 p = 1) : d577 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3393 (p : Pattern) (guard : d4117 p = 1) : d578 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d578, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d578, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d578, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d4117, d578, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3394 (p : Pattern) (guard : d4117 p = 1) : d579 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d579, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d579, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d579, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d579, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3395 (p : Pattern) (guard : d4203 p = 1) : d580 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d580, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d4203, d580, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d580, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d4203, d580, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3396 (p : Pattern) (guard : d4203 p = 1) : d581 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3389 p hg
    simpa only [d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3397 (p : Pattern) (guard : d4203 p = 1) : d582 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d4203, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4203, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3398 (p : Pattern) (guard : d4203 p = 1) : d583 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d583, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d4203, d583, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d583, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d583, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3399 (p : Pattern) (guard : d4203 p = 1) : d584 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d584, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d584, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d584, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3398 p hg
    simpa only [d584, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3400 (p : Pattern) (guard : d4203 p = 1) : d585 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d585, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d585, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d585, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d585, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3401 (p : Pattern) (guard : d4203 p = 1) : d586 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d586, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d586, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d586, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3400 p hg
    simpa only [d586, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3402 (p : Pattern) (guard : d4203 p = 1) : d587 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d587, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3387 p hg
    simpa only [d587, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d587, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3401 p hg
    simpa only [d587, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3403 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3404 (p : Pattern) (guard : d4117 p = 1) : d52 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3403 p hg
    simpa only [d4117, d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3405 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d185 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3406 (p : Pattern) (guard : d4117 p = 1) : d76 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d4117, d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3407 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3406 p hg
    simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3408 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d205 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3409 (p : Pattern) (guard : d4203 p = 1) : d553 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d553, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3407 p hg
    simpa only [d4203, d553, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d553, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3408 p hg
    simpa only [d4203, d553, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3410 (p : Pattern) (guard : d0 p = 1) : d595 p ≤ (0 : Int) + d196 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3411 (p : Pattern) (guard : d4117 p = 1) : d596 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d596, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d4117, d596, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d596, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d4117, d596, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3412 (p : Pattern) (guard : d0 p = 1) : d603 p ≤ (0 : Int) + d203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3413 (p : Pattern) (guard : d4117 p = 1) : d604 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d604, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d4117, d604, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d604, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3412 p hg
    simpa only [d4117, d604, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3414 (p : Pattern) (guard : d4117 p = 1) : d605 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d605, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d605, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d605, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3413 p hg
    simpa only [d605, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3415 (p : Pattern) (guard : d4203 p = 1) : d606 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d606, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d4203, d606, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d606, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d606, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3416 (p : Pattern) (guard : d4203 p = 1) : d607 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d607, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d607, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d607, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d607, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3417 (p : Pattern) (guard : d4203 p = 1) : d608 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d608, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d608, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d608, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d608, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3418 (p : Pattern) (guard : d4203 p = 1) : d609 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d609, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d609, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d609, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d609, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3419 (p : Pattern) (guard : d4117 p = 1) : d220 p ≤ (0 : Int) + d220 p := by
  omega
theorem compare3420 (p : Pattern) (guard : d4203 p = 1) : d610 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3419 p hg
    simpa only [d4203, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d4203, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3421 (p : Pattern) (guard : d0 p = 1) : d614 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3422 (p : Pattern) (guard : d4117 p = 1) : d615 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d615, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d615, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d615, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d4117, d615, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3423 (p : Pattern) (guard : d4117 p = 1) : d616 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d616, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d616, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d616, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3422 p hg
    simpa only [d616, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3424 (p : Pattern) (guard : d4203 p = 1) : d617 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d617, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3423 p hg
    simpa only [d4203, d617, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d617, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d4203, d617, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3425 (p : Pattern) (guard : d4203 p = 1) : d618 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3426 (p : Pattern) (guard : d0 p = 1) : d280 p ≤ (0 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3427 (p : Pattern) (guard : d4117 p = 1) : d281 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d281, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d281, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d281, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d4117, d281, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3428 (p : Pattern) (guard : d0 p = 1) : d288 p ≤ (0 : Int) + d238 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3429 (p : Pattern) (guard : d4117 p = 1) : d289 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d289, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d289, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d289, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d4117, d289, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3430 (p : Pattern) (guard : d4117 p = 1) : d290 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d290, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d290, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d290, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3429 p hg
    simpa only [d290, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3431 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d250 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3432 (p : Pattern) (guard : d4203 p = 1) : d619 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d619, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d4203, d619, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d619, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3431 p hg
    simpa only [d4203, d619, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3433 (p : Pattern) (guard : d0 p = 1) : d630 p ≤ (0 : Int) + d259 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3434 (p : Pattern) (guard : d4117 p = 1) : d631 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d631, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d4117, d631, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d631, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3433 p hg
    simpa only [d4117, d631, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3435 (p : Pattern) (guard : d0 p = 1) : d644 p ≤ (0 : Int) + d248 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3436 (p : Pattern) (guard : d4117 p = 1) : d645 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d4117, d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d4117, d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3437 (p : Pattern) (guard : d4117 p = 1) : d646 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d646, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3434 p hg
    simpa only [d646, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d646, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d646, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3438 (p : Pattern) (guard : d4203 p = 1) : d647 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d647, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3437 p hg
    simpa only [d4203, d647, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d647, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d647, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3439 (p : Pattern) (guard : d4203 p = 1) : d648 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d648, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3432 p hg
    simpa only [d648, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d648, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d648, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3440 (p : Pattern) (guard : d4203 p = 1) : d649 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d649, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3425 p hg
    simpa only [d649, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d649, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3439 p hg
    simpa only [d649, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3441 (p : Pattern) (guard : d4203 p = 1) : d650 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d650, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d650, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d650, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d650, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3442 (p : Pattern) (guard : d4203 p = 1) : d651 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d651, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3418 p hg
    simpa only [d651, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d651, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3441 p hg
    simpa only [d651, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3443 (p : Pattern) (guard : d4203 p = 1) : d652 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d652, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d652, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d652, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3442 p hg
    simpa only [d652, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3444 (p : Pattern) (guard : d0 p = 1) : d392 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3445 (p : Pattern) (guard : d4077 p = 1) : d653 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3444 p hg
    simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3446 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3447 (p : Pattern) (guard : d4077 p = 1) : d654 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3446 p hg
    simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3448 (p : Pattern) (guard : d4077 p = 1) : d655 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3445 p hg
    simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3447 p hg
    simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3449 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3450 (p : Pattern) (guard : d4077 p = 1) : d656 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3449 p hg
    simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3451 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3452 (p : Pattern) (guard : d4077 p = 1) : d657 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3453 (p : Pattern) (guard : d4077 p = 1) : d658 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3450 p hg
    simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3452 p hg
    simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3454 (p : Pattern) (guard : d4077 p = 1) : d659 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3448 p hg
    simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3453 p hg
    simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3455 (p : Pattern) (guard : d0 p = 1) : d397 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3456 (p : Pattern) (guard : d4077 p = 1) : d660 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3457 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3458 (p : Pattern) (guard : d4077 p = 1) : d661 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3457 p hg
    simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3459 (p : Pattern) (guard : d4077 p = 1) : d662 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3456 p hg
    simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3458 p hg
    simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3460 (p : Pattern) (guard : d0 p = 1) : d410 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3461 (p : Pattern) (guard : d4077 p = 1) : d663 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3460 p hg
    simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3462 (p : Pattern) (guard : d4077 p = 1) : d664 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3463 (p : Pattern) (guard : d4077 p = 1) : d665 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3462 p hg
    simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3464 (p : Pattern) (guard : d4077 p = 1) : d666 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3454 p hg
    simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3463 p hg
    simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3465 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3466 (p : Pattern) (guard : d4077 p = 1) : d667 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3465 p hg
    simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3467 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3468 (p : Pattern) (guard : d4077 p = 1) : d668 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3467 p hg
    simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3469 (p : Pattern) (guard : d4077 p = 1) : d669 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3466 p hg
    simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3470 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3471 (p : Pattern) (guard : d4077 p = 1) : d670 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3472 (p : Pattern) (guard : d4077 p = 1) : d671 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3447 p hg
    simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3471 p hg
    simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3473 (p : Pattern) (guard : d4077 p = 1) : d672 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3472 p hg
    simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3474 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3475 (p : Pattern) (guard : d4077 p = 1) : d673 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3474 p hg
    simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3476 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3477 (p : Pattern) (guard : d4077 p = 1) : d674 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3476 p hg
    simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3478 (p : Pattern) (guard : d4077 p = 1) : d675 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3475 p hg
    simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3477 p hg
    simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3479 (p : Pattern) (guard : d4077 p = 1) : d676 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3458 p hg
    simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3480 (p : Pattern) (guard : d4077 p = 1) : d677 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3478 p hg
    simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3479 p hg
    simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3481 (p : Pattern) (guard : d4077 p = 1) : d678 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3473 p hg
    simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3480 p hg
    simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3482 (p : Pattern) (guard : d4077 p = 1) : d679 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3464 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3481 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3483 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3484 (p : Pattern) (guard : d4077 p = 1) : d680 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3483 p hg
    simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3485 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3486 (p : Pattern) (guard : d4077 p = 1) : d681 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3485 p hg
    simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3487 (p : Pattern) (guard : d4077 p = 1) : d682 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3484 p hg
    simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3486 p hg
    simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3488 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3489 (p : Pattern) (guard : d4077 p = 1) : d683 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3488 p hg
    simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3490 (p : Pattern) (guard : d4077 p = 1) : d684 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3489 p hg
    simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3491 (p : Pattern) (guard : d4077 p = 1) : d685 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3487 p hg
    simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3490 p hg
    simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3492 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3493 (p : Pattern) (guard : d4077 p = 1) : d686 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3492 p hg
    simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3494 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3495 (p : Pattern) (guard : d4077 p = 1) : d687 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3494 p hg
    simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3496 (p : Pattern) (guard : d4077 p = 1) : d688 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3495 p hg
    simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3497 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3498 (p : Pattern) (guard : d4077 p = 1) : d689 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3497 p hg
    simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3499 (p : Pattern) (guard : d4077 p = 1) : d690 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3498 p hg
    simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
