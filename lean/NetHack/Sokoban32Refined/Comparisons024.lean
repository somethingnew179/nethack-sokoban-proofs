/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3360 (p : Pattern) (guard : d984 p = 1) : d313 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3322 p hg
    simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3359 p hg
    simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3361 (p : Pattern) (guard : d984 p = 1) : d314 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3357 p hg
    simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3360 p hg
    simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3362 (p : Pattern) (guard : d984 p = 1) : d322 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d322, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3348 p hg
    simpa only [d322, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d322, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3306 p hg
    simpa only [d322, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3363 (p : Pattern) (guard : d984 p = 1) : d323 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d323, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d323, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d323, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d323, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3364 (p : Pattern) (guard : d984 p = 1) : d324 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d324, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3362 p hg
    simpa only [d324, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d324, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3363 p hg
    simpa only [d324, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3365 (p : Pattern) (guard : d984 p = 1) : d325 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d325, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3361 p hg
    simpa only [d325, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d325, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3364 p hg
    simpa only [d325, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3366 (p : Pattern) (guard : d984 p = 1) : d326 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d326, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3351 p hg
    simpa only [d326, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d326, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3365 p hg
    simpa only [d326, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3367 (p : Pattern) (guard : d984 p = 1) : d327 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d327, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3340 p hg
    simpa only [d327, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d327, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d327, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3368 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3369 (p : Pattern) (guard : d912 p = 1) : d293 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3368 p hg
    simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3370 (p : Pattern) (guard : d0 p = 1) : d294 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3371 (p : Pattern) (guard : d912 p = 1) : d294 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3153 p hg
    simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3370 p hg
    simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3372 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3373 (p : Pattern) (guard : d912 p = 1) : d295 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3372 p hg
    simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3374 (p : Pattern) (guard : d912 p = 1) : d296 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3371 p hg
    simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3373 p hg
    simpa only [d296, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3375 (p : Pattern) (guard : d912 p = 1) : d297 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3374 p hg
    simpa only [d297, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3376 (p : Pattern) (guard : d0 p = 1) : d301 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3377 (p : Pattern) (guard : d913 p = 1) : d302 p ≤ (0 : Int) + d177 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d302, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3375 p hg
    simpa only [d913, d302, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d302, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3376 p hg
    simpa only [d913, d302, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3378 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d94 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3379 (p : Pattern) (guard : d912 p = 1) : d305 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d912, d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3378 p hg
    simpa only [d912, d305, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3380 (p : Pattern) (guard : d912 p = 1) : d306 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d306, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3381 (p : Pattern) (guard : d0 p = 1) : d307 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3382 (p : Pattern) (guard : d912 p = 1) : d307 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3381 p hg
    simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3383 (p : Pattern) (guard : d912 p = 1) : d308 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3380 p hg
    simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3382 p hg
    simpa only [d308, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3384 (p : Pattern) (guard : d0 p = 1) : d314 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3385 (p : Pattern) (guard : d913 p = 1) : d315 p ≤ (0 : Int) + d178 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d315, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d913, d315, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d315, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3384 p hg
    simpa only [d913, d315, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3386 (p : Pattern) (guard : d913 p = 1) : d316 p ≤ (0 : Int) + d179 p := by
  cases selected : p 86 with
  | false =>
    have hg : d913 p = 1 := by simpa only [d316, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3377 p hg
    simpa only [d316, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d913 p = 1 := by simpa only [d316, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3385 p hg
    simpa only [d316, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3387 (p : Pattern) (guard : d0 p = 1) : d298 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3388 (p : Pattern) (guard : d912 p = 1) : d299 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d912, d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3387 p hg
    simpa only [d912, d299, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3389 (p : Pattern) (guard : d912 p = 1) : d300 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3390 (p : Pattern) (guard : d912 p = 1) : d301 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3389 p hg
    simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3374 p hg
    simpa only [d301, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3391 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3392 (p : Pattern) (guard : d913 p = 1) : d321 p ≤ (0 : Int) + d180 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d321, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3390 p hg
    simpa only [d913, d321, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d321, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d913, d321, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3393 (p : Pattern) (guard : d0 p = 1) : d309 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3394 (p : Pattern) (guard : d912 p = 1) : d310 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3183 p hg
    simpa only [d912, d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d912, d310, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3395 (p : Pattern) (guard : d912 p = 1) : d311 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d311, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3396 (p : Pattern) (guard : d0 p = 1) : d312 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3397 (p : Pattern) (guard : d912 p = 1) : d312 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3187 p hg
    simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3398 (p : Pattern) (guard : d912 p = 1) : d313 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3382 p hg
    simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d313, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3399 (p : Pattern) (guard : d912 p = 1) : d314 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3398 p hg
    simpa only [d314, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3400 (p : Pattern) (guard : d0 p = 1) : d324 p ≤ (0 : Int) + d170 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3401 (p : Pattern) (guard : d913 p = 1) : d325 p ≤ (0 : Int) + d181 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d325, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d913, d325, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d325, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3400 p hg
    simpa only [d913, d325, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3402 (p : Pattern) (guard : d913 p = 1) : d326 p ≤ (0 : Int) + d182 p := by
  cases selected : p 86 with
  | false =>
    have hg : d913 p = 1 := by simpa only [d326, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d326, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d913 p = 1 := by simpa only [d326, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3401 p hg
    simpa only [d326, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3403 (p : Pattern) (guard : d913 p = 1) : d327 p ≤ (0 : Int) + d183 p := by
  cases selected : p 80 with
  | false =>
    have hg : d913 p = 1 := by simpa only [d327, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3386 p hg
    simpa only [d327, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d913 p = 1 := by simpa only [d327, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d327, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3404 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3405 (p : Pattern) (guard : d917 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d917, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d917, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3406 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare3407 (p : Pattern) (guard : d917 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3406 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3408 (p : Pattern) (guard : d917 p = 1) : d7 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3409 (p : Pattern) (guard : d917 p = 1) : d8 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3407 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3408 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3410 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3411 (p : Pattern) (guard : d917 p = 1) : d10 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d917, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d917, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3412 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare3413 (p : Pattern) (guard : d917 p = 1) : d12 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3412 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3414 (p : Pattern) (guard : d917 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3415 (p : Pattern) (guard : d917 p = 1) : d14 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3413 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3416 (p : Pattern) (guard : d917 p = 1) : d15 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3417 (p : Pattern) (guard : d917 p = 1) : d16 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3418 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3419 (p : Pattern) (guard : d1240 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3418 p hg
    simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3420 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d1240, d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1240, d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3421 (p : Pattern) (guard : d1240 p = 1) : d8 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3419 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3422 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3423 (p : Pattern) (guard : d1240 p = 1) : d12 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3422 p hg
    simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3424 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d1240, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1240, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3425 (p : Pattern) (guard : d1240 p = 1) : d14 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3423 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3426 (p : Pattern) (guard : d1240 p = 1) : d15 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3425 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3427 (p : Pattern) (guard : d1240 p = 1) : d16 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3428 (p : Pattern) (guard : d1241 p = 1) : d16 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3429 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3430 (p : Pattern) (guard : d1242 p = 1) : d293 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3429 p hg
    simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3431 (p : Pattern) (guard : d1241 p = 1) : d15 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3432 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d699 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3433 (p : Pattern) (guard : d1242 p = 1) : d294 p ≤ (0 : Int) + d699 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3431 p hg
    simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3432 p hg
    simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3434 (p : Pattern) (guard : d917 p = 1) : d52 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3435 (p : Pattern) (guard : d917 p = 1) : d53 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3434 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3436 (p : Pattern) (guard : d1240 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare3437 (p : Pattern) (guard : d1240 p = 1) : d52 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3438 (p : Pattern) (guard : d1240 p = 1) : d53 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3437 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3439 (p : Pattern) (guard : d1241 p = 1) : d53 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3440 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d702 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3441 (p : Pattern) (guard : d1242 p = 1) : d295 p ≤ (0 : Int) + d702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3439 p hg
    simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3442 (p : Pattern) (guard : d1242 p = 1) : d296 p ≤ (0 : Int) + d703 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d296, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3433 p hg
    simpa only [d296, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d296, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3441 p hg
    simpa only [d296, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3443 (p : Pattern) (guard : d1242 p = 1) : d297 p ≤ (0 : Int) + d704 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d297, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d297, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d297, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3442 p hg
    simpa only [d297, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3444 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3445 (p : Pattern) (guard : d1242 p = 1) : d293 p ≤ (0 : Int) + d707 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d293, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d1242, d293, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d293, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3444 p hg
    simpa only [d1242, d293, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3446 (p : Pattern) (guard : d1242 p = 1) : d293 p ≤ (0 : Int) + d708 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3445 p hg
    simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3447 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3448 (p : Pattern) (guard : d1242 p = 1) : d298 p ≤ (0 : Int) + d709 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d298, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d1242, d298, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d298, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3447 p hg
    simpa only [d1242, d298, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3449 (p : Pattern) (guard : d1242 p = 1) : d299 p ≤ (0 : Int) + d710 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d299, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d299, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d299, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3448 p hg
    simpa only [d299, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3450 (p : Pattern) (guard : d1242 p = 1) : d300 p ≤ (0 : Int) + d711 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d300, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3446 p hg
    simpa only [d300, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d300, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3449 p hg
    simpa only [d300, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3451 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3452 (p : Pattern) (guard : d1242 p = 1) : d294 p ≤ (0 : Int) + d712 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d294, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3431 p hg
    simpa only [d1242, d294, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d294, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1242, d294, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3453 (p : Pattern) (guard : d1242 p = 1) : d294 p ≤ (0 : Int) + d713 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3433 p hg
    simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3452 p hg
    simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3454 (p : Pattern) (guard : d1242 p = 1) : d295 p ≤ (0 : Int) + d714 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d295, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3439 p hg
    simpa only [d1242, d295, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d295, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1242, d295, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3455 (p : Pattern) (guard : d1242 p = 1) : d295 p ≤ (0 : Int) + d715 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3441 p hg
    simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3454 p hg
    simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3456 (p : Pattern) (guard : d1242 p = 1) : d296 p ≤ (0 : Int) + d716 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d296, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3453 p hg
    simpa only [d296, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d296, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d296, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3457 (p : Pattern) (guard : d1242 p = 1) : d301 p ≤ (0 : Int) + d717 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d301, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3450 p hg
    simpa only [d301, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d301, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3456 p hg
    simpa only [d301, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3458 (p : Pattern) (guard : d1242 p = 1) : d302 p ≤ (0 : Int) + d718 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d302, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3443 p hg
    simpa only [d302, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d302, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3457 p hg
    simpa only [d302, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3459 (p : Pattern) (guard : d917 p = 1) : d86 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3434 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3460 (p : Pattern) (guard : d1240 p = 1) : d86 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3437 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3461 (p : Pattern) (guard : d1241 p = 1) : d86 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3459 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3460 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3462 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d719 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3463 (p : Pattern) (guard : d1242 p = 1) : d303 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3462 p hg
    simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3464 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d719 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3465 (p : Pattern) (guard : d1242 p = 1) : d304 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3464 p hg
    simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3466 (p : Pattern) (guard : d1242 p = 1) : d305 p ≤ (0 : Int) + d719 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3463 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3465 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3467 (p : Pattern) (guard : d1242 p = 1) : d306 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d306, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d306, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d306, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3466 p hg
    simpa only [d306, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3468 (p : Pattern) (guard : d917 p = 1) : d97 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3469 (p : Pattern) (guard : d917 p = 1) : d98 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3470 (p : Pattern) (guard : d1240 p = 1) : d97 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3425 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3471 (p : Pattern) (guard : d1240 p = 1) : d98 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3425 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3472 (p : Pattern) (guard : d1241 p = 1) : d98 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3471 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3473 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3474 (p : Pattern) (guard : d1242 p = 1) : d307 p ≤ (0 : Int) + d706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3472 p hg
    simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3473 p hg
    simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3475 (p : Pattern) (guard : d1242 p = 1) : d308 p ≤ (0 : Int) + d721 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d308, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3467 p hg
    simpa only [d308, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d308, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3474 p hg
    simpa only [d308, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3476 (p : Pattern) (guard : d1242 p = 1) : d309 p ≤ (0 : Int) + d722 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d309, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d1242, d309, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d309, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1242, d309, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3477 (p : Pattern) (guard : d1242 p = 1) : d310 p ≤ (0 : Int) + d723 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d310, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3465 p hg
    simpa only [d310, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d310, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3476 p hg
    simpa only [d310, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3478 (p : Pattern) (guard : d1242 p = 1) : d311 p ≤ (0 : Int) + d724 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d311, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3449 p hg
    simpa only [d311, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d311, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3477 p hg
    simpa only [d311, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3479 (p : Pattern) (guard : d1242 p = 1) : d307 p ≤ (0 : Int) + d725 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d307, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3472 p hg
    simpa only [d1242, d307, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d307, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1242, d307, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3480 (p : Pattern) (guard : d1242 p = 1) : d307 p ≤ (0 : Int) + d726 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3474 p hg
    simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3479 p hg
    simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3481 (p : Pattern) (guard : d1241 p = 1) : d97 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3482 (p : Pattern) (guard : d1242 p = 1) : d312 p ≤ (0 : Int) + d705 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3481 p hg
    simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3483 (p : Pattern) (guard : d1242 p = 1) : d312 p ≤ (0 : Int) + d727 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d312, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3481 p hg
    simpa only [d1242, d312, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d312, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1242, d312, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3484 (p : Pattern) (guard : d1242 p = 1) : d312 p ≤ (0 : Int) + d728 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3482 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3483 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3485 (p : Pattern) (guard : d1242 p = 1) : d313 p ≤ (0 : Int) + d729 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d313, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3480 p hg
    simpa only [d313, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d313, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3484 p hg
    simpa only [d313, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3486 (p : Pattern) (guard : d1242 p = 1) : d314 p ≤ (0 : Int) + d730 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d314, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3478 p hg
    simpa only [d314, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d314, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3485 p hg
    simpa only [d314, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3487 (p : Pattern) (guard : d1242 p = 1) : d315 p ≤ (0 : Int) + d731 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d315, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3475 p hg
    simpa only [d315, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d315, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3486 p hg
    simpa only [d315, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3488 (p : Pattern) (guard : d1242 p = 1) : d316 p ≤ (0 : Int) + d732 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d316, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3458 p hg
    simpa only [d316, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d316, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3487 p hg
    simpa only [d316, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3489 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3490 (p : Pattern) (guard : d1242 p = 1) : d298 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3489 p hg
    simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3491 (p : Pattern) (guard : d1242 p = 1) : d299 p ≤ (0 : Int) + d700 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3490 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3492 (p : Pattern) (guard : d1242 p = 1) : d300 p ≤ (0 : Int) + d700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3491 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3493 (p : Pattern) (guard : d1242 p = 1) : d301 p ≤ (0 : Int) + d704 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d301, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3492 p hg
    simpa only [d301, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d301, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3442 p hg
    simpa only [d301, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3494 (p : Pattern) (guard : d1242 p = 1) : d317 p ≤ (0 : Int) + d709 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d317, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d1242, d317, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d317, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d1242, d317, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3495 (p : Pattern) (guard : d1242 p = 1) : d318 p ≤ (0 : Int) + d710 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d318, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3490 p hg
    simpa only [d318, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d318, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3494 p hg
    simpa only [d318, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3496 (p : Pattern) (guard : d1242 p = 1) : d319 p ≤ (0 : Int) + d710 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3449 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3495 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3497 (p : Pattern) (guard : d1242 p = 1) : d320 p ≤ (0 : Int) + d733 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d320, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d320, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d320, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3456 p hg
    simpa only [d320, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3498 (p : Pattern) (guard : d1242 p = 1) : d321 p ≤ (0 : Int) + d734 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d321, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d321, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d321, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3497 p hg
    simpa only [d321, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3499 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d719 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
