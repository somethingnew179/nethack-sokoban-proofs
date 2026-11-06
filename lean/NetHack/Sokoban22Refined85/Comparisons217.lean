/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons216
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30380 (p : Pattern) (guard : d5847 p = 1) : d3597 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30379 p hg
    simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23453 p hg
    simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30381 (p : Pattern) (guard : d5847 p = 1) : d3598 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30380 p hg
    simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23453 p hg
    simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30382 (p : Pattern) (guard : d5847 p = 1) : d3599 p ≤ (0 : Int) + d3258 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3599, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30381 p hg
    simpa only [d3599, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3599, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3599, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30383 (p : Pattern) (guard : d5847 p = 1) : d3600 p ≤ (0 : Int) + d3259 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3600, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d3600, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3600, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30382 p hg
    simpa only [d3600, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30384 (p : Pattern) (guard : d5847 p = 1) : d3601 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3601, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3601, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3601, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d3601, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30385 (p : Pattern) (guard : d5847 p = 1) : d3602 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30384 p hg
    simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30386 (p : Pattern) (guard : d5847 p = 1) : d339 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d339, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d339, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d339, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d339, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30387 (p : Pattern) (guard : d5847 p = 1) : d3603 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30332 p hg
    simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30386 p hg
    simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30388 (p : Pattern) (guard : d5847 p = 1) : d3604 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30385 p hg
    simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30387 p hg
    simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30389 (p : Pattern) (guard : d5847 p = 1) : d3605 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30388 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30390 (p : Pattern) (guard : d5847 p = 1) : d3606 p ≤ (0 : Int) + d3260 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3606, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30389 p hg
    simpa only [d3606, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3606, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3606, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30391 (p : Pattern) (guard : d5847 p = 1) : d3607 p ≤ (0 : Int) + d3261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3607, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30383 p hg
    simpa only [d3607, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3607, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30390 p hg
    simpa only [d3607, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30392 (p : Pattern) (guard : d5847 p = 1) : d3608 p ≤ (0 : Int) + d3262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3608, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30378 p hg
    simpa only [d3608, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3608, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30391 p hg
    simpa only [d3608, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30393 (p : Pattern) (guard : d5847 p = 1) : d3609 p ≤ (0 : Int) + d3263 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3609, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d3609, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3609, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3609, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30394 (p : Pattern) (guard : d5847 p = 1) : d3610 p ≤ (0 : Int) + d3264 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3610, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30393 p hg
    simpa only [d3610, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3610, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30390 p hg
    simpa only [d3610, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30395 (p : Pattern) (guard : d5847 p = 1) : d3611 p ≤ (0 : Int) + d3265 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3611, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30346 p hg
    simpa only [d3611, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3611, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3611, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30396 (p : Pattern) (guard : d5847 p = 1) : d3612 p ≤ (0 : Int) + d3266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3612, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30395 p hg
    simpa only [d3612, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3612, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3612, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30397 (p : Pattern) (guard : d5847 p = 1) : d3613 p ≤ (0 : Int) + d3267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3613, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30394 p hg
    simpa only [d3613, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3613, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30396 p hg
    simpa only [d3613, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30398 (p : Pattern) (guard : d5847 p = 1) : d3614 p ≤ (0 : Int) + d3268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3614, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30392 p hg
    simpa only [d3614, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3614, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30397 p hg
    simpa only [d3614, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30399 (p : Pattern) (guard : d5847 p = 1) : d3615 p ≤ (0 : Int) + d3269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3615, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30354 p hg
    simpa only [d3615, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3615, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30398 p hg
    simpa only [d3615, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30400 (p : Pattern) (guard : d5847 p = 1) : d3616 p ≤ (0 : Int) + d3270 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3616, d3270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29317 p hg
    simpa only [d5847, d3616, d3270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3616, d3270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17696 p hg
    simpa only [d5847, d3616, d3270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30401 (p : Pattern) (guard : d5847 p = 1) : d3617 p ≤ (0 : Int) + d3271 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3617, d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30400 p hg
    simpa only [d3617, d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3617, d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3617, d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30402 (p : Pattern) (guard : d5847 p = 1) : d3618 p ≤ (0 : Int) + d3272 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3618, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30401 p hg
    simpa only [d3618, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3618, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3618, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30403 (p : Pattern) (guard : d5847 p = 1) : d3619 p ≤ (0 : Int) + d3273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3619, d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30402 p hg
    simpa only [d3619, d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3619, d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d3619, d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30404 (p : Pattern) (guard : d5847 p = 1) : d3620 p ≤ (0 : Int) + d3274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3620, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30403 p hg
    simpa only [d3620, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3620, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30321 p hg
    simpa only [d3620, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30405 (p : Pattern) (guard : d5847 p = 1) : d3621 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30364 p hg
    simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30406 (p : Pattern) (guard : d5847 p = 1) : d3622 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30405 p hg
    simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30364 p hg
    simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30407 (p : Pattern) (guard : d5847 p = 1) : d3623 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30406 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30408 (p : Pattern) (guard : d5847 p = 1) : d3624 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3624, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3624, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3624, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d3624, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30409 (p : Pattern) (guard : d5847 p = 1) : d3625 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30408 p hg
    simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30410 (p : Pattern) (guard : d5847 p = 1) : d3626 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30409 p hg
    simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30408 p hg
    simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30411 (p : Pattern) (guard : d5847 p = 1) : d3627 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3627, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30410 p hg
    simpa only [d3627, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3627, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3627, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30412 (p : Pattern) (guard : d5847 p = 1) : d3628 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3628, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30407 p hg
    simpa only [d3628, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3628, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30411 p hg
    simpa only [d3628, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30413 (p : Pattern) (guard : d5847 p = 1) : d3629 p ≤ (0 : Int) + d3276 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3629, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30404 p hg
    simpa only [d3629, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3629, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30412 p hg
    simpa only [d3629, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30414 (p : Pattern) (guard : d5847 p = 1) : d3630 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3630, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30340 p hg
    simpa only [d3630, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3630, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30351 p hg
    simpa only [d3630, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30415 (p : Pattern) (guard : d5847 p = 1) : d3631 p ≤ (0 : Int) + d3278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3631, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30413 p hg
    simpa only [d3631, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3631, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30414 p hg
    simpa only [d3631, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30416 (p : Pattern) (guard : d5847 p = 1) : d57 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30417 (p : Pattern) (guard : d5847 p = 1) : d3632 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30416 p hg
    simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23495 p hg
    simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30418 (p : Pattern) (guard : d5847 p = 1) : d3633 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30417 p hg
    simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23495 p hg
    simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30419 (p : Pattern) (guard : d5847 p = 1) : d3634 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30416 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30418 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30420 (p : Pattern) (guard : d5847 p = 1) : d3635 p ≤ (0 : Int) + d3280 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3635, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30418 p hg
    simpa only [d3635, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3635, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3635, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30421 (p : Pattern) (guard : d5847 p = 1) : d3636 p ≤ (0 : Int) + d3281 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3636, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30419 p hg
    simpa only [d3636, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3636, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30420 p hg
    simpa only [d3636, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30422 (p : Pattern) (guard : d5847 p = 1) : d3637 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3637, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30340 p hg
    simpa only [d3637, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3637, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d3637, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30423 (p : Pattern) (guard : d5847 p = 1) : d3638 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30379 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30381 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30424 (p : Pattern) (guard : d5847 p = 1) : d3639 p ≤ (0 : Int) + d3283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3639, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30423 p hg
    simpa only [d3639, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3639, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30382 p hg
    simpa only [d3639, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30425 (p : Pattern) (guard : d5847 p = 1) : d3640 p ≤ (0 : Int) + d3284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3640, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d3640, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3640, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3640, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30426 (p : Pattern) (guard : d5847 p = 1) : d3641 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3641, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30422 p hg
    simpa only [d3641, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3641, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d3641, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30427 (p : Pattern) (guard : d5847 p = 1) : d3642 p ≤ (0 : Int) + d3286 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3642, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30415 p hg
    simpa only [d3642, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3642, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30426 p hg
    simpa only [d3642, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30428 (p : Pattern) (guard : d5847 p = 1) : d3643 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30367 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30429 (p : Pattern) (guard : d5847 p = 1) : d3644 p ≤ (0 : Int) + d3287 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3644, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30428 p hg
    simpa only [d3644, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3644, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3644, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30430 (p : Pattern) (guard : d5847 p = 1) : d3645 p ≤ (0 : Int) + d3288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3645, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30377 p hg
    simpa only [d3645, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3645, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30429 p hg
    simpa only [d3645, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30431 (p : Pattern) (guard : d5847 p = 1) : d3646 p ≤ (0 : Int) + d3289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3646, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30390 p hg
    simpa only [d3646, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3646, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30395 p hg
    simpa only [d3646, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30432 (p : Pattern) (guard : d5847 p = 1) : d3647 p ≤ (0 : Int) + d3290 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3647, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30430 p hg
    simpa only [d3647, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3647, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30431 p hg
    simpa only [d3647, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30433 (p : Pattern) (guard : d5847 p = 1) : d3648 p ≤ (0 : Int) + d3291 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3648, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30419 p hg
    simpa only [d3648, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3648, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3648, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30434 (p : Pattern) (guard : d5847 p = 1) : d3649 p ≤ (0 : Int) + d3292 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3649, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30390 p hg
    simpa only [d3649, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3649, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30433 p hg
    simpa only [d3649, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30435 (p : Pattern) (guard : d5847 p = 1) : d3650 p ≤ (0 : Int) + d3293 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3650, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30423 p hg
    simpa only [d3650, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3650, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3650, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30436 (p : Pattern) (guard : d5847 p = 1) : d3651 p ≤ (0 : Int) + d3294 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3651, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30435 p hg
    simpa only [d3651, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3651, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3651, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30437 (p : Pattern) (guard : d5847 p = 1) : d3652 p ≤ (0 : Int) + d3295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3652, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30434 p hg
    simpa only [d3652, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3652, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30436 p hg
    simpa only [d3652, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30438 (p : Pattern) (guard : d5847 p = 1) : d3653 p ≤ (0 : Int) + d3296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3653, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30432 p hg
    simpa only [d3653, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3653, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30437 p hg
    simpa only [d3653, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30439 (p : Pattern) (guard : d5847 p = 1) : d3654 p ≤ (0 : Int) + d3297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3654, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30427 p hg
    simpa only [d3654, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3654, d3297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30438 p hg
    simpa only [d3654, d3297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30440 (p : Pattern) (guard : d5847 p = 1) : d3655 p ≤ (0 : Int) + d3298 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3655, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30399 p hg
    simpa only [d3655, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3655, d3298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30439 p hg
    simpa only [d3655, d3298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30441 (p : Pattern) (guard : d5847 p = 1) : d3656 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30314 p hg
    simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30355 p hg
    simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30442 (p : Pattern) (guard : d5847 p = 1) : d3657 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30356 p hg
    simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30441 p hg
    simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30443 (p : Pattern) (guard : d5847 p = 1) : d3658 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30442 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30444 (p : Pattern) (guard : d5847 p = 1) : d3659 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3659, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d3659, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3659, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3659, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30445 (p : Pattern) (guard : d5847 p = 1) : d3660 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3660, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30443 p hg
    simpa only [d3660, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3660, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30444 p hg
    simpa only [d3660, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30446 (p : Pattern) (guard : d5847 p = 1) : d3661 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3661, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30447 (p : Pattern) (guard : d5847 p = 1) : d3662 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30314 p hg
    simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30446 p hg
    simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30448 (p : Pattern) (guard : d5847 p = 1) : d3663 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30356 p hg
    simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30447 p hg
    simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30449 (p : Pattern) (guard : d5847 p = 1) : d3664 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3664, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30448 p hg
    simpa only [d3664, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3664, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3664, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30450 (p : Pattern) (guard : d5847 p = 1) : d3665 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3665, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d3665, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3665, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30449 p hg
    simpa only [d3665, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30451 (p : Pattern) (guard : d5847 p = 1) : d3666 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30445 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30450 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30452 (p : Pattern) (guard : d5847 p = 1) : d3667 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3667, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30359 p hg
    simpa only [d3667, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3667, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3667, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30453 (p : Pattern) (guard : d5847 p = 1) : d3668 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3668, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d3668, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3668, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30452 p hg
    simpa only [d3668, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30454 (p : Pattern) (guard : d5847 p = 1) : d3669 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3669, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30388 p hg
    simpa only [d3669, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3669, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3669, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30455 (p : Pattern) (guard : d5847 p = 1) : d3670 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3670, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30389 p hg
    simpa only [d3670, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3670, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30454 p hg
    simpa only [d3670, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30456 (p : Pattern) (guard : d5847 p = 1) : d3671 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3671, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30453 p hg
    simpa only [d3671, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3671, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30455 p hg
    simpa only [d3671, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30457 (p : Pattern) (guard : d5847 p = 1) : d3672 p ≤ (0 : Int) + d3299 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3672, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30451 p hg
    simpa only [d3672, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3672, d3299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30456 p hg
    simpa only [d3672, d3299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30458 (p : Pattern) (guard : d5847 p = 1) : d3673 p ≤ (0 : Int) + d3245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3673, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30345 p hg
    simpa only [d3673, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3673, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3673, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30459 (p : Pattern) (guard : d5847 p = 1) : d3674 p ≤ (0 : Int) + d3246 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3674, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30346 p hg
    simpa only [d3674, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3674, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30458 p hg
    simpa only [d3674, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30460 (p : Pattern) (guard : d5847 p = 1) : d3675 p ≤ (0 : Int) + d3247 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3675, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d3675, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3675, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3675, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30461 (p : Pattern) (guard : d5847 p = 1) : d3676 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3676, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30456 p hg
    simpa only [d3676, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3676, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30460 p hg
    simpa only [d3676, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30462 (p : Pattern) (guard : d5847 p = 1) : d3677 p ≤ (0 : Int) + d3300 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3677, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30457 p hg
    simpa only [d3677, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3677, d3300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30461 p hg
    simpa only [d3677, d3300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30463 (p : Pattern) (guard : d5847 p = 1) : d3678 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3678, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30428 p hg
    simpa only [d3678, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3678, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30368 p hg
    simpa only [d3678, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30464 (p : Pattern) (guard : d5847 p = 1) : d3679 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30370 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30375 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30465 (p : Pattern) (guard : d5847 p = 1) : d3680 p ≤ (0 : Int) + d3301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3680, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30464 p hg
    simpa only [d3680, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3680, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30376 p hg
    simpa only [d3680, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30466 (p : Pattern) (guard : d5847 p = 1) : d3681 p ≤ (0 : Int) + d3302 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3681, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30463 p hg
    simpa only [d3681, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3681, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30465 p hg
    simpa only [d3681, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30467 (p : Pattern) (guard : d5847 p = 1) : d3682 p ≤ (0 : Int) + d3303 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3682, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30466 p hg
    simpa only [d3682, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3682, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d3682, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30468 (p : Pattern) (guard : d5847 p = 1) : d3683 p ≤ (0 : Int) + d3304 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3683, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30467 p hg
    simpa only [d3683, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3683, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3683, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30469 (p : Pattern) (guard : d5847 p = 1) : d3684 p ≤ (0 : Int) + d3305 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3684, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30462 p hg
    simpa only [d3684, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3684, d3305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30468 p hg
    simpa only [d3684, d3305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30470 (p : Pattern) (guard : d5847 p = 1) : d3685 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3685, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30450 p hg
    simpa only [d3685, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3685, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30463 p hg
    simpa only [d3685, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30471 (p : Pattern) (guard : d5847 p = 1) : d3686 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3686, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30455 p hg
    simpa only [d3686, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3686, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d3686, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30472 (p : Pattern) (guard : d5847 p = 1) : d3687 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3687, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30470 p hg
    simpa only [d3687, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3687, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30471 p hg
    simpa only [d3687, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30473 (p : Pattern) (guard : d5847 p = 1) : d3688 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3688, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30455 p hg
    simpa only [d3688, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3688, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d3688, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30474 (p : Pattern) (guard : d5847 p = 1) : d3689 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3689, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30473 p hg
    simpa only [d3689, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3689, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d3689, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30475 (p : Pattern) (guard : d5847 p = 1) : d3690 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3690, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30472 p hg
    simpa only [d3690, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3690, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30474 p hg
    simpa only [d3690, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30476 (p : Pattern) (guard : d5847 p = 1) : d3691 p ≤ (0 : Int) + d3309 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3691, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30465 p hg
    simpa only [d3691, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3691, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3691, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30477 (p : Pattern) (guard : d5847 p = 1) : d3692 p ≤ (0 : Int) + d3310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3692, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30476 p hg
    simpa only [d3692, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3692, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3692, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30478 (p : Pattern) (guard : d5847 p = 1) : d3693 p ≤ (0 : Int) + d3311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3693, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30477 p hg
    simpa only [d3693, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3693, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3693, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30479 (p : Pattern) (guard : d5847 p = 1) : d3694 p ≤ (0 : Int) + d3312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3694, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30475 p hg
    simpa only [d3694, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3694, d3312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30478 p hg
    simpa only [d3694, d3312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30480 (p : Pattern) (guard : d5847 p = 1) : d3695 p ≤ (0 : Int) + d3313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3695, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30469 p hg
    simpa only [d3695, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3695, d3313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30479 p hg
    simpa only [d3695, d3313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30481 (p : Pattern) (guard : d5847 p = 1) : d3696 p ≤ (0 : Int) + d3314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3696, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30440 p hg
    simpa only [d3696, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3696, d3314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d3696, d3314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30482 (p : Pattern) (guard : d5847 p = 1) : d3697 p ≤ (0 : Int) + d3315 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3697, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d3697, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3697, d3315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d3697, d3315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30483 (p : Pattern) (guard : d5847 p = 1) : d3698 p ≤ (0 : Int) + d3316 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3698, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30482 p hg
    simpa only [d3698, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3698, d3316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d3698, d3316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30484 (p : Pattern) (guard : d5847 p = 1) : d3699 p ≤ (0 : Int) + d3317 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3699, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d3699, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3699, d3317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3699, d3317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30485 (p : Pattern) (guard : d5847 p = 1) : d3700 p ≤ (0 : Int) + d3318 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3700, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30483 p hg
    simpa only [d3700, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3700, d3318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30484 p hg
    simpa only [d3700, d3318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30486 (p : Pattern) (guard : d5847 p = 1) : d3701 p ≤ (0 : Int) + d3319 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3701, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30484 p hg
    simpa only [d3701, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3701, d3319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3701, d3319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30487 (p : Pattern) (guard : d5847 p = 1) : d3702 p ≤ (0 : Int) + d3320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3702, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30485 p hg
    simpa only [d3702, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3702, d3320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30486 p hg
    simpa only [d3702, d3320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30488 (p : Pattern) (guard : d5847 p = 1) : d3703 p ≤ (0 : Int) + d3321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3703, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30486 p hg
    simpa only [d3703, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3703, d3321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3703, d3321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30489 (p : Pattern) (guard : d5847 p = 1) : d3704 p ≤ (0 : Int) + d3322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3704, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30487 p hg
    simpa only [d3704, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3704, d3322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30488 p hg
    simpa only [d3704, d3322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30490 (p : Pattern) (guard : d5847 p = 1) : d3705 p ≤ (0 : Int) + d3323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3705, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d3705, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3705, d3323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30489 p hg
    simpa only [d3705, d3323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30491 (p : Pattern) (guard : d5847 p = 1) : d3706 p ≤ (0 : Int) + d3324 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3706, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30481 p hg
    simpa only [d3706, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3706, d3324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30490 p hg
    simpa only [d3706, d3324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30492 (p : Pattern) (guard : d5847 p = 1) : d3553 p ≤ (0 : Int) + d3325 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30327 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30330 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30493 (p : Pattern) (guard : d5847 p = 1) : d3707 p ≤ (0 : Int) + d3326 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3707, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30492 p hg
    simpa only [d3707, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3707, d3326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30341 p hg
    simpa only [d3707, d3326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30494 (p : Pattern) (guard : d5847 p = 1) : d3708 p ≤ (0 : Int) + d3327 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3708, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30493 p hg
    simpa only [d3708, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3708, d3327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30353 p hg
    simpa only [d3708, d3327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30495 (p : Pattern) (guard : d5847 p = 1) : d3709 p ≤ (0 : Int) + d3328 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3709, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30494 p hg
    simpa only [d3709, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3709, d3328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30398 p hg
    simpa only [d3709, d3328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30496 (p : Pattern) (guard : d5847 p = 1) : d3710 p ≤ (0 : Int) + d3306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3710, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30330 p hg
    simpa only [d3710, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3710, d3306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30412 p hg
    simpa only [d3710, d3306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30497 (p : Pattern) (guard : d5847 p = 1) : d3711 p ≤ (0 : Int) + d3307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3711, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30496 p hg
    simpa only [d3711, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3711, d3307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30414 p hg
    simpa only [d3711, d3307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30498 (p : Pattern) (guard : d5847 p = 1) : d3712 p ≤ (0 : Int) + d3308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3712, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30497 p hg
    simpa only [d3712, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3712, d3308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30426 p hg
    simpa only [d3712, d3308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30499 (p : Pattern) (guard : d5847 p = 1) : d3713 p ≤ (0 : Int) + d3329 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3713, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30498 p hg
    simpa only [d3713, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3713, d3329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30438 p hg
    simpa only [d3713, d3329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30500 (p : Pattern) (guard : d5847 p = 1) : d3714 p ≤ (0 : Int) + d3330 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3714, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30495 p hg
    simpa only [d3714, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3714, d3330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30499 p hg
    simpa only [d3714, d3330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30501 (p : Pattern) (guard : d5847 p = 1) : d3715 p ≤ (0 : Int) + d3331 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3715, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30500 p hg
    simpa only [d3715, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3715, d3331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d3715, d3331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30502 (p : Pattern) (guard : d5847 p = 1) : d3716 p ≤ (0 : Int) + d3332 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3716, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d3716, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3716, d3332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3716, d3332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30503 (p : Pattern) (guard : d5847 p = 1) : d3717 p ≤ (0 : Int) + d3333 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3717, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30501 p hg
    simpa only [d3717, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3717, d3333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30502 p hg
    simpa only [d3717, d3333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30504 (p : Pattern) (guard : d5847 p = 1) : d3718 p ≤ (0 : Int) + d3334 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3718, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30491 p hg
    simpa only [d3718, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3718, d3334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30503 p hg
    simpa only [d3718, d3334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30505 (p : Pattern) (guard : d5847 p = 1) : d3719 p ≤ (0 : Int) + d3335 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3719, d3335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29435 p hg
    simpa only [d5847, d3719, d3335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3719, d3335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17763 p hg
    simpa only [d5847, d3719, d3335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30506 (p : Pattern) (guard : d5847 p = 1) : d3720 p ≤ (0 : Int) + d3336 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3720, d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30505 p hg
    simpa only [d3720, d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3720, d3336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3720, d3336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30507 (p : Pattern) (guard : d5847 p = 1) : d3721 p ≤ (0 : Int) + d3337 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3721, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30506 p hg
    simpa only [d3721, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3721, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3721, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30508 (p : Pattern) (guard : d5847 p = 1) : d3722 p ≤ (0 : Int) + d3338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3722, d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30507 p hg
    simpa only [d3722, d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3722, d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d3722, d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30509 (p : Pattern) (guard : d5847 p = 1) : d3723 p ≤ (0 : Int) + d3339 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3723, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30508 p hg
    simpa only [d3723, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3723, d3339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30321 p hg
    simpa only [d3723, d3339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30510 (p : Pattern) (guard : d5847 p = 1) : d3724 p ≤ (0 : Int) + d3340 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3724, d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30509 p hg
    simpa only [d3724, d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3724, d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30330 p hg
    simpa only [d3724, d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30511 (p : Pattern) (guard : d5847 p = 1) : d3725 p ≤ (0 : Int) + d3341 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3725, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30510 p hg
    simpa only [d3725, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3725, d3341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30341 p hg
    simpa only [d3725, d3341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30512 (p : Pattern) (guard : d5847 p = 1) : d3726 p ≤ (0 : Int) + d3342 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3726, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30511 p hg
    simpa only [d3726, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3726, d3342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30353 p hg
    simpa only [d3726, d3342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30513 (p : Pattern) (guard : d5847 p = 1) : d3727 p ≤ (0 : Int) + d3343 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3727, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30512 p hg
    simpa only [d3727, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3727, d3343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30398 p hg
    simpa only [d3727, d3343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30514 (p : Pattern) (guard : d5847 p = 1) : d3710 p ≤ (0 : Int) + d3344 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3710, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30327 p hg
    simpa only [d3710, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3710, d3344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30412 p hg
    simpa only [d3710, d3344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30515 (p : Pattern) (guard : d5847 p = 1) : d3711 p ≤ (0 : Int) + d3345 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3711, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30514 p hg
    simpa only [d3711, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3711, d3345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30414 p hg
    simpa only [d3711, d3345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30516 (p : Pattern) (guard : d5847 p = 1) : d3712 p ≤ (0 : Int) + d3346 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3712, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30515 p hg
    simpa only [d3712, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3712, d3346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30426 p hg
    simpa only [d3712, d3346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30517 (p : Pattern) (guard : d5847 p = 1) : d3713 p ≤ (0 : Int) + d3347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3713, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30516 p hg
    simpa only [d3713, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3713, d3347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30438 p hg
    simpa only [d3713, d3347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30518 (p : Pattern) (guard : d5847 p = 1) : d3728 p ≤ (0 : Int) + d3348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3728, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30513 p hg
    simpa only [d3728, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3728, d3348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30517 p hg
    simpa only [d3728, d3348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30519 (p : Pattern) (guard : d5847 p = 1) : d3729 p ≤ (0 : Int) + d3349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3729, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30518 p hg
    simpa only [d3729, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3729, d3349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d3729, d3349, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
