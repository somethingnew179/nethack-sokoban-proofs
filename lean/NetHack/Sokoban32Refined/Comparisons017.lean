/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2380 (p : Pattern) (guard : d873 p = 1) : d42 p ≤ (0 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d42, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d42, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d42, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d42, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2381 (p : Pattern) (guard : d873 p = 1) : d43 p ≤ (0 : Int) + d549 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d43, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d43, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d43, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d43, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2382 (p : Pattern) (guard : d873 p = 1) : d44 p ≤ (0 : Int) + d555 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d44, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2374 p hg
    simpa only [d44, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d44, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2381 p hg
    simpa only [d44, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2383 (p : Pattern) (guard : d873 p = 1) : d45 p ≤ (0 : Int) + d556 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d45, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d45, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d45, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d45, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2384 (p : Pattern) (guard : d873 p = 1) : d46 p ≤ (0 : Int) + d557 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d46, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d46, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d46, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d46, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2385 (p : Pattern) (guard : d873 p = 1) : d47 p ≤ (0 : Int) + d558 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d47, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d47, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d47, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2384 p hg
    simpa only [d47, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2386 (p : Pattern) (guard : d873 p = 1) : d48 p ≤ (0 : Int) + d559 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d48, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d48, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d48, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d48, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2387 (p : Pattern) (guard : d873 p = 1) : d49 p ≤ (0 : Int) + d557 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d49, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d49, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d49, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d49, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2388 (p : Pattern) (guard : d873 p = 1) : d50 p ≤ (0 : Int) + d560 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d50, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2386 p hg
    simpa only [d50, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d50, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2387 p hg
    simpa only [d50, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2389 (p : Pattern) (guard : d873 p = 1) : d51 p ≤ (0 : Int) + d561 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d51, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d51, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d51, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d51, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2390 (p : Pattern) (guard : d873 p = 1) : d52 p ≤ (0 : Int) + d562 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2391 (p : Pattern) (guard : d873 p = 1) : d53 p ≤ (0 : Int) + d563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2392 (p : Pattern) (guard : d873 p = 1) : d54 p ≤ (0 : Int) + d564 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d54, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d54, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d54, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d54, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2393 (p : Pattern) (guard : d873 p = 1) : d55 p ≤ (0 : Int) + d565 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d55, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d55, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d55, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d55, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2394 (p : Pattern) (guard : d873 p = 1) : d56 p ≤ (0 : Int) + d566 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d56, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d56, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d56, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2393 p hg
    simpa only [d56, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2395 (p : Pattern) (guard : d873 p = 1) : d57 p ≤ (0 : Int) + d567 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d57, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d57, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d57, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2394 p hg
    simpa only [d57, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2396 (p : Pattern) (guard : d873 p = 1) : d58 p ≤ (0 : Int) + d568 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d58, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d58, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d58, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d58, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2397 (p : Pattern) (guard : d873 p = 1) : d59 p ≤ (0 : Int) + d569 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d59, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d59, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d59, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d59, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2398 (p : Pattern) (guard : d873 p = 1) : d60 p ≤ (0 : Int) + d570 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d60, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d60, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d60, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d60, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2399 (p : Pattern) (guard : d873 p = 1) : d61 p ≤ (0 : Int) + d562 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d61, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d61, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d61, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d61, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2400 (p : Pattern) (guard : d873 p = 1) : d62 p ≤ (0 : Int) + d563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d62, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d62, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d62, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d62, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2401 (p : Pattern) (guard : d873 p = 1) : d63 p ≤ (0 : Int) + d566 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d63, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d63, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d63, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2393 p hg
    simpa only [d63, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2402 (p : Pattern) (guard : d873 p = 1) : d64 p ≤ (0 : Int) + d571 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d64, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2398 p hg
    simpa only [d64, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d64, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2401 p hg
    simpa only [d64, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2403 (p : Pattern) (guard : d873 p = 1) : d65 p ≤ (0 : Int) + d572 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d65, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d65, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d65, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d65, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2404 (p : Pattern) (guard : d873 p = 1) : d66 p ≤ (0 : Int) + d573 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d66, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2389 p hg
    simpa only [d66, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d66, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2403 p hg
    simpa only [d66, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2405 (p : Pattern) (guard : d873 p = 1) : d67 p ≤ (0 : Int) + d574 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d67, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2383 p hg
    simpa only [d67, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d67, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2404 p hg
    simpa only [d67, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2406 (p : Pattern) (guard : d873 p = 1) : d27 p ≤ (0 : Int) + d575 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d27, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d27, d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d27, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d27, d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2407 (p : Pattern) (guard : d873 p = 1) : d68 p ≤ (0 : Int) + d576 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d68, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d68, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d68, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d68, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2408 (p : Pattern) (guard : d873 p = 1) : d69 p ≤ (0 : Int) + d577 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d69, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d69, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d69, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2407 p hg
    simpa only [d69, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2409 (p : Pattern) (guard : d873 p = 1) : d70 p ≤ (0 : Int) + d578 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d70, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d70, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d70, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d70, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2410 (p : Pattern) (guard : d873 p = 1) : d71 p ≤ (0 : Int) + d579 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d71, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d71, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d71, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2409 p hg
    simpa only [d71, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2411 (p : Pattern) (guard : d873 p = 1) : d72 p ≤ (0 : Int) + d580 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d72, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2408 p hg
    simpa only [d72, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d72, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d72, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2412 (p : Pattern) (guard : d873 p = 1) : d73 p ≤ (0 : Int) + d581 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d73, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2406 p hg
    simpa only [d73, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d73, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d73, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2413 (p : Pattern) (guard : d873 p = 1) : d74 p ≤ (0 : Int) + d582 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d74, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d74, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d74, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2412 p hg
    simpa only [d74, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2414 (p : Pattern) (guard : d873 p = 1) : d8 p ≤ (0 : Int) + d583 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2349 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2415 (p : Pattern) (guard : d873 p = 1) : d16 p ≤ (0 : Int) + d584 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2416 (p : Pattern) (guard : d873 p = 1) : d27 p ≤ (0 : Int) + d585 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d27, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d27, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d27, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d27, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2417 (p : Pattern) (guard : d873 p = 1) : d75 p ≤ (0 : Int) + d586 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d75, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2407 p hg
    simpa only [d75, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d75, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2409 p hg
    simpa only [d75, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2418 (p : Pattern) (guard : d873 p = 1) : d76 p ≤ (0 : Int) + d587 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d76, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2416 p hg
    simpa only [d76, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d76, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d76, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2419 (p : Pattern) (guard : d873 p = 1) : d77 p ≤ (0 : Int) + d588 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d77, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d77, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d77, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2418 p hg
    simpa only [d77, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2420 (p : Pattern) (guard : d873 p = 1) : d78 p ≤ (0 : Int) + d589 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d78, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2413 p hg
    simpa only [d78, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d78, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d78, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2421 (p : Pattern) (guard : d873 p = 1) : d79 p ≤ (0 : Int) + d590 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d79, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2384 p hg
    simpa only [d79, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d79, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d79, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2422 (p : Pattern) (guard : d873 p = 1) : d80 p ≤ (0 : Int) + d591 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d80, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d80, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d80, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d80, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2423 (p : Pattern) (guard : d873 p = 1) : d81 p ≤ (0 : Int) + d592 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d81, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2394 p hg
    simpa only [d81, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d81, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d81, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2424 (p : Pattern) (guard : d873 p = 1) : d82 p ≤ (0 : Int) + d593 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d82, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d82, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d82, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2423 p hg
    simpa only [d82, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2425 (p : Pattern) (guard : d873 p = 1) : d83 p ≤ (0 : Int) + d594 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d83, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2422 p hg
    simpa only [d83, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d83, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2424 p hg
    simpa only [d83, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2426 (p : Pattern) (guard : d873 p = 1) : d84 p ≤ (0 : Int) + d595 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d84, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2420 p hg
    simpa only [d84, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d84, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2425 p hg
    simpa only [d84, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2427 (p : Pattern) (guard : d873 p = 1) : d85 p ≤ (0 : Int) + d596 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d85, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2405 p hg
    simpa only [d85, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d85, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2426 p hg
    simpa only [d85, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2428 (p : Pattern) (guard : d873 p = 1) : d86 p ≤ (0 : Int) + d597 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d86, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2349 p hg
    simpa only [d86, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d86, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d86, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2429 (p : Pattern) (guard : d873 p = 1) : d86 p ≤ (0 : Int) + d598 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2430 (p : Pattern) (guard : d873 p = 1) : d86 p ≤ (0 : Int) + d599 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2428 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2431 (p : Pattern) (guard : d873 p = 1) : d87 p ≤ (0 : Int) + d600 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d87, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d87, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d87, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d87, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2432 (p : Pattern) (guard : d873 p = 1) : d88 p ≤ (0 : Int) + d601 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d88, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d88, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d88, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2431 p hg
    simpa only [d88, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2433 (p : Pattern) (guard : d873 p = 1) : d89 p ≤ (0 : Int) + d602 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d89, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2430 p hg
    simpa only [d89, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d89, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d89, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2434 (p : Pattern) (guard : d873 p = 1) : d86 p ≤ (0 : Int) + d603 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2435 (p : Pattern) (guard : d873 p = 1) : d90 p ≤ (0 : Int) + d604 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d90, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d90, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d90, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d90, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2436 (p : Pattern) (guard : d873 p = 1) : d91 p ≤ (0 : Int) + d605 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d91, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2434 p hg
    simpa only [d91, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d91, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2435 p hg
    simpa only [d91, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2437 (p : Pattern) (guard : d873 p = 1) : d92 p ≤ (0 : Int) + d598 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d92, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d92, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d92, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d92, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2438 (p : Pattern) (guard : d873 p = 1) : d93 p ≤ (0 : Int) + d601 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d93, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2437 p hg
    simpa only [d93, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d93, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2431 p hg
    simpa only [d93, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2439 (p : Pattern) (guard : d873 p = 1) : d94 p ≤ (0 : Int) + d606 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d94, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2436 p hg
    simpa only [d94, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d94, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2438 p hg
    simpa only [d94, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2440 (p : Pattern) (guard : d873 p = 1) : d95 p ≤ (0 : Int) + d607 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d95, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d95, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d95, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2439 p hg
    simpa only [d95, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2441 (p : Pattern) (guard : d873 p = 1) : d96 p ≤ (0 : Int) + d608 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d96, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2383 p hg
    simpa only [d96, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d96, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d96, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2442 (p : Pattern) (guard : d873 p = 1) : d97 p ≤ (0 : Int) + d576 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2354 p hg
    simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2443 (p : Pattern) (guard : d873 p = 1) : d98 p ≤ (0 : Int) + d577 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2354 p hg
    simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2444 (p : Pattern) (guard : d873 p = 1) : d99 p ≤ (0 : Int) + d580 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d99, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2443 p hg
    simpa only [d99, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d99, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d99, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2445 (p : Pattern) (guard : d873 p = 1) : d100 p ≤ (0 : Int) + d609 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d100, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2443 p hg
    simpa only [d100, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d100, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d100, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2446 (p : Pattern) (guard : d873 p = 1) : d101 p ≤ (0 : Int) + d580 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2447 (p : Pattern) (guard : d873 p = 1) : d102 p ≤ (0 : Int) + d610 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2446 p hg
    simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2448 (p : Pattern) (guard : d873 p = 1) : d103 p ≤ (0 : Int) + d611 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2441 p hg
    simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2447 p hg
    simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2449 (p : Pattern) (guard : d873 p = 1) : d86 p ≤ (0 : Int) + d612 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2434 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2450 (p : Pattern) (guard : d873 p = 1) : d89 p ≤ (0 : Int) + d613 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d89, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2449 p hg
    simpa only [d89, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d89, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d89, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2451 (p : Pattern) (guard : d873 p = 1) : d104 p ≤ (0 : Int) + d614 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d104, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d104, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d104, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d104, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2452 (p : Pattern) (guard : d873 p = 1) : d105 p ≤ (0 : Int) + d615 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d105, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d105, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d105, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2451 p hg
    simpa only [d105, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2453 (p : Pattern) (guard : d873 p = 1) : d106 p ≤ (0 : Int) + d616 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d106, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d106, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d106, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2452 p hg
    simpa only [d106, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2454 (p : Pattern) (guard : d873 p = 1) : d107 p ≤ (0 : Int) + d617 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d107, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d107, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d107, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d107, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2455 (p : Pattern) (guard : d873 p = 1) : d108 p ≤ (0 : Int) + d618 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d108, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d108, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d108, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d108, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2456 (p : Pattern) (guard : d873 p = 1) : d109 p ≤ (0 : Int) + d586 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d109, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d109, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d109, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2409 p hg
    simpa only [d109, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2457 (p : Pattern) (guard : d873 p = 1) : d110 p ≤ (0 : Int) + d619 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d110, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d110, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d110, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d110, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2458 (p : Pattern) (guard : d873 p = 1) : d111 p ≤ (0 : Int) + d620 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d111, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d111, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d111, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d111, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2459 (p : Pattern) (guard : d873 p = 1) : d112 p ≤ (0 : Int) + d621 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d112, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d112, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d112, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2458 p hg
    simpa only [d112, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2460 (p : Pattern) (guard : d873 p = 1) : d113 p ≤ (0 : Int) + d622 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d113, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2455 p hg
    simpa only [d113, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d113, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2459 p hg
    simpa only [d113, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2461 (p : Pattern) (guard : d873 p = 1) : d114 p ≤ (0 : Int) + d623 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d114, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2453 p hg
    simpa only [d114, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d114, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d114, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2462 (p : Pattern) (guard : d873 p = 1) : d115 p ≤ (0 : Int) + d624 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d115, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2448 p hg
    simpa only [d115, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d115, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2461 p hg
    simpa only [d115, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2463 (p : Pattern) (guard : d873 p = 1) : d116 p ≤ (0 : Int) + d625 p := by
  cases selected : p 86 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d116, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2427 p hg
    simpa only [d116, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d116, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d116, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2464 (p : Pattern) (guard : d873 p = 1) : d36 p ≤ (0 : Int) + d626 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d36, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d36, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d36, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2373 p hg
    simpa only [d36, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2465 (p : Pattern) (guard : d873 p = 1) : d44 p ≤ (0 : Int) + d627 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d44, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d44, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d44, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2381 p hg
    simpa only [d44, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2466 (p : Pattern) (guard : d873 p = 1) : d45 p ≤ (0 : Int) + d628 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d45, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d45, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d45, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2465 p hg
    simpa only [d45, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2467 (p : Pattern) (guard : d873 p = 1) : d45 p ≤ (0 : Int) + d629 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2383 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2466 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2468 (p : Pattern) (guard : d873 p = 1) : d67 p ≤ (0 : Int) + d630 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d67, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d67, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d67, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2404 p hg
    simpa only [d67, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2469 (p : Pattern) (guard : d873 p = 1) : d16 p ≤ (0 : Int) + d631 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2357 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2470 (p : Pattern) (guard : d873 p = 1) : d28 p ≤ (0 : Int) + d632 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d28, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d28, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d28, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d28, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2471 (p : Pattern) (guard : d873 p = 1) : d76 p ≤ (0 : Int) + d633 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d76, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d76, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d76, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d76, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2472 (p : Pattern) (guard : d873 p = 1) : d77 p ≤ (0 : Int) + d634 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d77, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2470 p hg
    simpa only [d77, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d77, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2471 p hg
    simpa only [d77, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2473 (p : Pattern) (guard : d873 p = 1) : d77 p ≤ (0 : Int) + d635 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2472 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2474 (p : Pattern) (guard : d873 p = 1) : d117 p ≤ (0 : Int) + d636 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d117, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2473 p hg
    simpa only [d117, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d117, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2425 p hg
    simpa only [d117, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2475 (p : Pattern) (guard : d873 p = 1) : d118 p ≤ (0 : Int) + d637 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d118, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2468 p hg
    simpa only [d118, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d118, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2474 p hg
    simpa only [d118, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2476 (p : Pattern) (guard : d873 p = 1) : d119 p ≤ (0 : Int) + d638 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d119, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d119, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d119, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d119, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2477 (p : Pattern) (guard : d873 p = 1) : d120 p ≤ (0 : Int) + d639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d120, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2476 p hg
    simpa only [d120, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d120, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d120, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2478 (p : Pattern) (guard : d873 p = 1) : d121 p ≤ (0 : Int) + d640 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d121, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d121, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d121, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2477 p hg
    simpa only [d121, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2479 (p : Pattern) (guard : d873 p = 1) : d122 p ≤ (0 : Int) + d641 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d122, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2478 p hg
    simpa only [d122, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d122, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2438 p hg
    simpa only [d122, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2480 (p : Pattern) (guard : d873 p = 1) : d123 p ≤ (0 : Int) + d642 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d123, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d123, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d123, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2479 p hg
    simpa only [d123, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2481 (p : Pattern) (guard : d873 p = 1) : d124 p ≤ (0 : Int) + d643 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d124, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2466 p hg
    simpa only [d124, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d124, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d124, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2482 (p : Pattern) (guard : d873 p = 1) : d125 p ≤ (0 : Int) + d586 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2483 (p : Pattern) (guard : d873 p = 1) : d126 p ≤ (0 : Int) + d644 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d126, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d126, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d126, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d126, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2484 (p : Pattern) (guard : d873 p = 1) : d127 p ≤ (0 : Int) + d645 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d127, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2447 p hg
    simpa only [d127, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d127, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d127, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2485 (p : Pattern) (guard : d873 p = 1) : d128 p ≤ (0 : Int) + d646 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d128, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d128, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d128, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d128, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2486 (p : Pattern) (guard : d873 p = 1) : d129 p ≤ (0 : Int) + d647 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d129, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2472 p hg
    simpa only [d129, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d129, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2424 p hg
    simpa only [d129, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2487 (p : Pattern) (guard : d873 p = 1) : d130 p ≤ (0 : Int) + d648 p := by
  cases selected : p 113 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d130, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2459 p hg
    simpa only [d130, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d130, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d130, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2488 (p : Pattern) (guard : d873 p = 1) : d131 p ≤ (0 : Int) + d649 p := by
  cases selected : p 112 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d131, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d131, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d131, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2487 p hg
    simpa only [d131, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2489 (p : Pattern) (guard : d873 p = 1) : d132 p ≤ (0 : Int) + d650 p := by
  cases selected : p 106 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d132, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d132, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d132, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d132, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2490 (p : Pattern) (guard : d873 p = 1) : d133 p ≤ (0 : Int) + d651 p := by
  cases selected : p 86 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d133, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d133, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d133, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2489 p hg
    simpa only [d133, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2491 (p : Pattern) (guard : d873 p = 1) : d134 p ≤ (0 : Int) + d652 p := by
  cases selected : p 80 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d134, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d134, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d134, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2490 p hg
    simpa only [d134, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2492 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2493 (p : Pattern) (guard : d841 p = 1) : d256 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2492 p hg
    simpa only [d841, d256, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2494 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2495 (p : Pattern) (guard : d841 p = 1) : d257 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d841, d257, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2496 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2497 (p : Pattern) (guard : d841 p = 1) : d258 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d258, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d258, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d258, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2496 p hg
    simpa only [d841, d258, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2498 (p : Pattern) (guard : d841 p = 1) : d259 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d259, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2495 p hg
    simpa only [d259, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d259, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2497 p hg
    simpa only [d259, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2499 (p : Pattern) (guard : d841 p = 1) : d260 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d260, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d260, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d260, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2498 p hg
    simpa only [d260, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2500 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2501 (p : Pattern) (guard : d870 p = 1) : d266 p ≤ (0 : Int) + d177 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d266, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d870, d266, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d266, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2500 p hg
    simpa only [d870, d266, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2502 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d94 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2503 (p : Pattern) (guard : d841 p = 1) : d267 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d267, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d841, d267, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d267, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2502 p hg
    simpa only [d841, d267, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2504 (p : Pattern) (guard : d841 p = 1) : d268 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d268, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d268, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d268, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d268, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2505 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2506 (p : Pattern) (guard : d841 p = 1) : d269 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d269, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d841, d269, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d269, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2505 p hg
    simpa only [d841, d269, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2507 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2508 (p : Pattern) (guard : d841 p = 1) : d270 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d841, d270, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2509 (p : Pattern) (guard : d841 p = 1) : d271 p ≤ (0 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2506 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2510 (p : Pattern) (guard : d841 p = 1) : d272 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d272, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2504 p hg
    simpa only [d272, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d272, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d272, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2511 (p : Pattern) (guard : d0 p = 1) : d277 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2512 (p : Pattern) (guard : d870 p = 1) : d278 p ≤ (0 : Int) + d178 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d278, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d870, d278, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d278, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d870, d278, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2513 (p : Pattern) (guard : d870 p = 1) : d279 p ≤ (0 : Int) + d179 p := by
  cases selected : p 86 with
  | false =>
    have hg : d870 p = 1 := by simpa only [d279, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2501 p hg
    simpa only [d279, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d870 p = 1 := by simpa only [d279, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d279, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2514 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2515 (p : Pattern) (guard : d841 p = 1) : d261 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2514 p hg
    simpa only [d841, d261, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2516 (p : Pattern) (guard : d841 p = 1) : d262 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2517 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2518 (p : Pattern) (guard : d841 p = 1) : d263 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2517 p hg
    simpa only [d841, d263, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2519 (p : Pattern) (guard : d841 p = 1) : d264 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2495 p hg
    simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d264, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
