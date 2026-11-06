/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18480 (p : Pattern) (guard : d4902 p = 1) : d2352 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18479 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18481 (p : Pattern) (guard : d4902 p = 1) : d2353 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18480 p hg
    simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18447 p hg
    simpa only [d2353, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18482 (p : Pattern) (guard : d4902 p = 1) : d2354 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18463 p hg
    simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18464 p hg
    simpa only [d2354, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18483 (p : Pattern) (guard : d4902 p = 1) : d2355 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18481 p hg
    simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2355, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18484 (p : Pattern) (guard : d4902 p = 1) : d2356 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18457 p hg
    simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18362 p hg
    simpa only [d2356, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18485 (p : Pattern) (guard : d4902 p = 1) : d2357 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18483 p hg
    simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18484 p hg
    simpa only [d2357, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18486 (p : Pattern) (guard : d4902 p = 1) : d2358 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18457 p hg
    simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d2358, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18487 (p : Pattern) (guard : d4902 p = 1) : d2359 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18486 p hg
    simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2359, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18488 (p : Pattern) (guard : d4902 p = 1) : d2360 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18485 p hg
    simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18487 p hg
    simpa only [d2360, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18489 (p : Pattern) (guard : d4902 p = 1) : d2361 p ≤ (2 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18463 p hg
    simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2361, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18490 (p : Pattern) (guard : d4902 p = 1) : d2362 p ≤ (2 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18468 p hg
    simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18489 p hg
    simpa only [d2362, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18491 (p : Pattern) (guard : d4902 p = 1) : d2363 p ≤ (2 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18471 p hg
    simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18372 p hg
    simpa only [d2363, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18492 (p : Pattern) (guard : d4902 p = 1) : d2364 p ≤ (2 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18490 p hg
    simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18491 p hg
    simpa only [d2364, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18493 (p : Pattern) (guard : d4902 p = 1) : d2365 p ≤ (2 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18471 p hg
    simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18374 p hg
    simpa only [d2365, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18494 (p : Pattern) (guard : d4902 p = 1) : d2366 p ≤ (2 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18493 p hg
    simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2366, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18495 (p : Pattern) (guard : d4902 p = 1) : d2367 p ≤ (2 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18492 p hg
    simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18494 p hg
    simpa only [d2367, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18496 (p : Pattern) (guard : d4902 p = 1) : d2368 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18488 p hg
    simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18495 p hg
    simpa only [d2368, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18497 (p : Pattern) (guard : d4902 p = 1) : d2369 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18477 p hg
    simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18496 p hg
    simpa only [d2369, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18498 (p : Pattern) (guard : d4902 p = 1) : d2370 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18458 p hg
    simpa only [d2370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18499 (p : Pattern) (guard : d4902 p = 1) : d2371 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18498 p hg
    simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18461 p hg
    simpa only [d2371, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18500 (p : Pattern) (guard : d4902 p = 1) : d2372 p ≤ (2 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18466 p hg
    simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18467 p hg
    simpa only [d2372, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18501 (p : Pattern) (guard : d4902 p = 1) : d2373 p ≤ (2 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18500 p hg
    simpa only [d2373, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18502 (p : Pattern) (guard : d4902 p = 1) : d2374 p ≤ (2 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18501 p hg
    simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2374, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18503 (p : Pattern) (guard : d4902 p = 1) : d2375 p ≤ (2 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18502 p hg
    simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2375, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18504 (p : Pattern) (guard : d4902 p = 1) : d2376 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18499 p hg
    simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18503 p hg
    simpa only [d2376, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18505 (p : Pattern) (guard : d4902 p = 1) : d2377 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2377, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18506 (p : Pattern) (guard : d4902 p = 1) : d2378 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18505 p hg
    simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18484 p hg
    simpa only [d2378, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18507 (p : Pattern) (guard : d4902 p = 1) : d2379 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18506 p hg
    simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18487 p hg
    simpa only [d2379, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18508 (p : Pattern) (guard : d4902 p = 1) : d2380 p ≤ (2 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18500 p hg
    simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2380, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18509 (p : Pattern) (guard : d4902 p = 1) : d2381 p ≤ (2 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18508 p hg
    simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2381, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18510 (p : Pattern) (guard : d4902 p = 1) : d2382 p ≤ (2 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18509 p hg
    simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2382, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18511 (p : Pattern) (guard : d4902 p = 1) : d2383 p ≤ (2 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18507 p hg
    simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18510 p hg
    simpa only [d2383, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18512 (p : Pattern) (guard : d4902 p = 1) : d2384 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18504 p hg
    simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18511 p hg
    simpa only [d2384, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18513 (p : Pattern) (guard : d4902 p = 1) : d2385 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18497 p hg
    simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18512 p hg
    simpa only [d2385, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18514 (p : Pattern) (guard : d4902 p = 1) : d2386 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18460 p hg
    simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2386, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18515 (p : Pattern) (guard : d4902 p = 1) : d2387 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18514 p hg
    simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2387, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18516 (p : Pattern) (guard : d4902 p = 1) : d2388 p ≤ (2 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18515 p hg
    simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2388, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18517 (p : Pattern) (guard : d4902 p = 1) : d2389 p ≤ (2 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18516 p hg
    simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2389, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18518 (p : Pattern) (guard : d4902 p = 1) : d2390 p ≤ (2 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18512 p hg
    simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18517 p hg
    simpa only [d2390, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18519 (p : Pattern) (guard : d4902 p = 1) : d2391 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18513 p hg
    simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18518 p hg
    simpa only [d2391, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18520 (p : Pattern) (guard : d4902 p = 1) : d2392 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18452 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18521 (p : Pattern) (guard : d4902 p = 1) : d2393 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18520 p hg
    simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18458 p hg
    simpa only [d2393, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18522 (p : Pattern) (guard : d4902 p = 1) : d2394 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18521 p hg
    simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18461 p hg
    simpa only [d2394, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18523 (p : Pattern) (guard : d4902 p = 1) : d2395 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18522 p hg
    simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18476 p hg
    simpa only [d2395, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18524 (p : Pattern) (guard : d4902 p = 1) : d2396 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18507 p hg
    simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18495 p hg
    simpa only [d2396, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18525 (p : Pattern) (guard : d4902 p = 1) : d2397 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18523 p hg
    simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18524 p hg
    simpa only [d2397, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18526 (p : Pattern) (guard : d4902 p = 1) : d2398 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18525 p hg
    simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18512 p hg
    simpa only [d2398, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18527 (p : Pattern) (guard : d4902 p = 1) : d2399 p ≤ (2 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18512 p hg
    simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2399, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18528 (p : Pattern) (guard : d4902 p = 1) : d2400 p ≤ (2 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18526 p hg
    simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18527 p hg
    simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18529 (p : Pattern) (guard : d4902 p = 1) : d2401 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18519 p hg
    simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18528 p hg
    simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18530 (p : Pattern) (guard : d4902 p = 1) : d2402 p ≤ (2 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18420 p hg
    simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18529 p hg
    simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18531 (p : Pattern) (guard : d4902 p = 1) : d2403 p ≤ (2 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18442 p hg
    simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18530 p hg
    simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18532 (p : Pattern) (guard : d4902 p = 1) : d2404 p ≤ (2 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18332 p hg
    simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18336 p hg
    simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18533 (p : Pattern) (guard : d4902 p = 1) : d2405 p ≤ (2 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18532 p hg
    simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18534 (p : Pattern) (guard : d4902 p = 1) : d2406 p ≤ (2 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18332 p hg
    simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18340 p hg
    simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18535 (p : Pattern) (guard : d4902 p = 1) : d2407 p ≤ (2 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18335 p hg
    simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18536 (p : Pattern) (guard : d4902 p = 1) : d2408 p ≤ (2 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18534 p hg
    simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18535 p hg
    simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18537 (p : Pattern) (guard : d4902 p = 1) : d2409 p ≤ (2 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18533 p hg
    simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18536 p hg
    simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18538 (p : Pattern) (guard : d4902 p = 1) : d2410 p ≤ (2 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18368 p hg
    simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18535 p hg
    simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18539 (p : Pattern) (guard : d4902 p = 1) : d2411 p ≤ (2 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18538 p hg
    simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18375 p hg
    simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18540 (p : Pattern) (guard : d4902 p = 1) : d2412 p ≤ (2 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18537 p hg
    simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18539 p hg
    simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18541 (p : Pattern) (guard : d4902 p = 1) : d2413 p ≤ (2 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18398 p hg
    simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18540 p hg
    simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18542 (p : Pattern) (guard : d4902 p = 1) : d2414 p ≤ (2 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18532 p hg
    simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18543 (p : Pattern) (guard : d4902 p = 1) : d2415 p ≤ (2 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18535 p hg
    simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18374 p hg
    simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18544 (p : Pattern) (guard : d4902 p = 1) : d2416 p ≤ (2 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18542 p hg
    simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18543 p hg
    simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18545 (p : Pattern) (guard : d4902 p = 1) : d2417 p ≤ (2 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18535 p hg
    simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18546 (p : Pattern) (guard : d4902 p = 1) : d2418 p ≤ (2 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18545 p hg
    simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18547 (p : Pattern) (guard : d4902 p = 1) : d2419 p ≤ (2 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18544 p hg
    simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18546 p hg
    simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18548 (p : Pattern) (guard : d4902 p = 1) : d2420 p ≤ (2 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18389 p hg
    simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18547 p hg
    simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18549 (p : Pattern) (guard : d4902 p = 1) : d2421 p ≤ (2 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18541 p hg
    simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18548 p hg
    simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18550 (p : Pattern) (guard : d4902 p = 1) : d2422 p ≤ (2 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18383 p hg
    simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18551 (p : Pattern) (guard : d4902 p = 1) : d2423 p ≤ (2 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18550 p hg
    simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18384 p hg
    simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18552 (p : Pattern) (guard : d4902 p = 1) : d2424 p ≤ (2 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13406 p hg
    simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16131 p hg
    simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18553 (p : Pattern) (guard : d4902 p = 1) : d2425 p ≤ (2 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18552 p hg
    simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18554 (p : Pattern) (guard : d4902 p = 1) : d2426 p ≤ (2 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18552 p hg
    simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18553 p hg
    simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18555 (p : Pattern) (guard : d4902 p = 1) : d2427 p ≤ (2 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18554 p hg
    simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18556 (p : Pattern) (guard : d4902 p = 1) : d2428 p ≤ (2 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18555 p hg
    simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18557 (p : Pattern) (guard : d4902 p = 1) : d2429 p ≤ (2 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18556 p hg
    simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18558 (p : Pattern) (guard : d4902 p = 1) : d2430 p ≤ (2 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18551 p hg
    simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18557 p hg
    simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18559 (p : Pattern) (guard : d4902 p = 1) : d2431 p ≤ (2 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18560 (p : Pattern) (guard : d4902 p = 1) : d2432 p ≤ (2 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18559 p hg
    simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18561 (p : Pattern) (guard : d4902 p = 1) : d2433 p ≤ (2 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18560 p hg
    simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18391 p hg
    simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18562 (p : Pattern) (guard : d4902 p = 1) : d2434 p ≤ (2 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18554 p hg
    simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18563 (p : Pattern) (guard : d4902 p = 1) : d2435 p ≤ (2 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18562 p hg
    simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18564 (p : Pattern) (guard : d4902 p = 1) : d2436 p ≤ (2 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18563 p hg
    simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18565 (p : Pattern) (guard : d4902 p = 1) : d2437 p ≤ (2 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18561 p hg
    simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18564 p hg
    simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18566 (p : Pattern) (guard : d4902 p = 1) : d2438 p ≤ (2 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18558 p hg
    simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18565 p hg
    simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18567 (p : Pattern) (guard : d4902 p = 1) : d2439 p ≤ (2 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18549 p hg
    simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18566 p hg
    simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18568 (p : Pattern) (guard : d4902 p = 1) : d2440 p ≤ (2 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18566 p hg
    simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18569 (p : Pattern) (guard : d4902 p = 1) : d2441 p ≤ (2 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18567 p hg
    simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18568 p hg
    simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18570 (p : Pattern) (guard : d4902 p = 1) : d2442 p ≤ (2 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18436 p hg
    simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18569 p hg
    simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18571 (p : Pattern) (guard : d4902 p = 1) : d2443 p ≤ (2 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18420 p hg
    simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18570 p hg
    simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18572 (p : Pattern) (guard : d4902 p = 1) : d2444 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18457 p hg
    simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18573 (p : Pattern) (guard : d4902 p = 1) : d2445 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18483 p hg
    simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18572 p hg
    simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18574 (p : Pattern) (guard : d4902 p = 1) : d2446 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18572 p hg
    simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18575 (p : Pattern) (guard : d4902 p = 1) : d2447 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18573 p hg
    simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18574 p hg
    simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18576 (p : Pattern) (guard : d4902 p = 1) : d2448 p ≤ (2 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18471 p hg
    simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18577 (p : Pattern) (guard : d4902 p = 1) : d2449 p ≤ (2 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18490 p hg
    simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18576 p hg
    simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18578 (p : Pattern) (guard : d4902 p = 1) : d2450 p ≤ (2 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18576 p hg
    simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18579 (p : Pattern) (guard : d4902 p = 1) : d2451 p ≤ (2 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18577 p hg
    simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18578 p hg
    simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18580 (p : Pattern) (guard : d4902 p = 1) : d2452 p ≤ (2 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18575 p hg
    simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18579 p hg
    simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18581 (p : Pattern) (guard : d4902 p = 1) : d2453 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18477 p hg
    simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18580 p hg
    simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18582 (p : Pattern) (guard : d4902 p = 1) : d2454 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18505 p hg
    simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18572 p hg
    simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18583 (p : Pattern) (guard : d4902 p = 1) : d2455 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18582 p hg
    simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18574 p hg
    simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18584 (p : Pattern) (guard : d4902 p = 1) : d2456 p ≤ (2 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18583 p hg
    simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18510 p hg
    simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18585 (p : Pattern) (guard : d4902 p = 1) : d2457 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18504 p hg
    simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18584 p hg
    simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18586 (p : Pattern) (guard : d4902 p = 1) : d2458 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18581 p hg
    simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18585 p hg
    simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18587 (p : Pattern) (guard : d4902 p = 1) : d2459 p ≤ (2 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18585 p hg
    simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18517 p hg
    simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18588 (p : Pattern) (guard : d4902 p = 1) : d2460 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18586 p hg
    simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18587 p hg
    simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18589 (p : Pattern) (guard : d4902 p = 1) : d2461 p ≤ (2 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18463 p hg
    simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18467 p hg
    simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18590 (p : Pattern) (guard : d4902 p = 1) : d2462 p ≤ (2 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18589 p hg
    simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18591 (p : Pattern) (guard : d4902 p = 1) : d2463 p ≤ (2 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18590 p hg
    simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18576 p hg
    simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18592 (p : Pattern) (guard : d4902 p = 1) : d2464 p ≤ (2 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18466 p hg
    simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18593 (p : Pattern) (guard : d4902 p = 1) : d2465 p ≤ (2 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18592 p hg
    simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18594 (p : Pattern) (guard : d4902 p = 1) : d2466 p ≤ (2 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18593 p hg
    simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18595 (p : Pattern) (guard : d4902 p = 1) : d2467 p ≤ (2 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18591 p hg
    simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18594 p hg
    simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18596 (p : Pattern) (guard : d4902 p = 1) : d2468 p ≤ (2 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18522 p hg
    simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18595 p hg
    simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18597 (p : Pattern) (guard : d4902 p = 1) : d2469 p ≤ (2 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18455 p hg
    simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18467 p hg
    simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18598 (p : Pattern) (guard : d4902 p = 1) : d2470 p ≤ (2 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18597 p hg
    simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18471 p hg
    simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18599 (p : Pattern) (guard : d4902 p = 1) : d2471 p ≤ (2 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18598 p hg
    simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18593 p hg
    simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18600 (p : Pattern) (guard : d4902 p = 1) : d2472 p ≤ (2 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18348 p hg
    simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18601 (p : Pattern) (guard : d4902 p = 1) : d2473 p ≤ (2 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18599 p hg
    simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18600 p hg
    simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18602 (p : Pattern) (guard : d4902 p = 1) : d2474 p ≤ (2 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18583 p hg
    simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18601 p hg
    simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18603 (p : Pattern) (guard : d4902 p = 1) : d2475 p ≤ (2 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18596 p hg
    simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18602 p hg
    simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18604 (p : Pattern) (guard : d4902 p = 1) : d2476 p ≤ (2 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18605 (p : Pattern) (guard : d4902 p = 1) : d2477 p ≤ (2 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18604 p hg
    simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18606 (p : Pattern) (guard : d4902 p = 1) : d2478 p ≤ (2 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18605 p hg
    simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18487 p hg
    simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18607 (p : Pattern) (guard : d4902 p = 1) : d2479 p ≤ (2 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18606 p hg
    simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18510 p hg
    simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18608 (p : Pattern) (guard : d4902 p = 1) : d2480 p ≤ (2 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18572 p hg
    simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18609 (p : Pattern) (guard : d4902 p = 1) : d2481 p ≤ (2 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18608 p hg
    simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18509 p hg
    simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18610 (p : Pattern) (guard : d4902 p = 1) : d2482 p ≤ (2 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18329 p hg
    simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18611 (p : Pattern) (guard : d4902 p = 1) : d2483 p ≤ (2 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18610 p hg
    simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18612 (p : Pattern) (guard : d4902 p = 1) : d2484 p ≤ (2 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18609 p hg
    simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18611 p hg
    simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18613 (p : Pattern) (guard : d4902 p = 1) : d2485 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18607 p hg
    simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18612 p hg
    simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18614 (p : Pattern) (guard : d4902 p = 1) : d2486 p ≤ (2 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18603 p hg
    simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18613 p hg
    simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18615 (p : Pattern) (guard : d4902 p = 1) : d2487 p ≤ (2 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18328 p hg
    simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18616 (p : Pattern) (guard : d4902 p = 1) : d2488 p ≤ (2 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18615 p hg
    simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18617 (p : Pattern) (guard : d4902 p = 1) : d2489 p ≤ (2 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18457 p hg
    simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18328 p hg
    simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18618 (p : Pattern) (guard : d4902 p = 1) : d2490 p ≤ (2 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18617 p hg
    simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18619 (p : Pattern) (guard : d4902 p = 1) : d2491 p ≤ (2 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18616 p hg
    simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18618 p hg
    simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
