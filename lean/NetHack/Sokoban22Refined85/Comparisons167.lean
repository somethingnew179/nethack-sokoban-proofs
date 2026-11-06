/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons166
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23380 (p : Pattern) (guard : d5855 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare23381 (p : Pattern) (guard : d5855 p = 1) : d2511 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2511, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23379 p hg
    simpa only [d2511, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2511, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2511, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23382 (p : Pattern) (guard : d5855 p = 1) : d2512 p ≤ (0 : Int) + d3231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2512, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23374 p hg
    simpa only [d2512, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2512, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d2512, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23383 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23384 (p : Pattern) (guard : d5851 p = 1) : d2513 p ≤ (0 : Int) + d3233 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2513, d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17653 p hg
    simpa only [d5851, d2513, d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2513, d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d5851, d2513, d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23385 (p : Pattern) (guard : d5855 p = 1) : d2514 p ≤ (0 : Int) + d3234 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2514, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d5855, d2514, d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2514, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23366 p hg
    simpa only [d5855, d2514, d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23386 (p : Pattern) (guard : d5855 p = 1) : d2515 p ≤ (0 : Int) + d3235 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2515, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d2515, d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2515, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d2515, d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23387 (p : Pattern) (guard : d5855 p = 1) : d2516 p ≤ (0 : Int) + d3236 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2516, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23386 p hg
    simpa only [d2516, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2516, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d2516, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23388 (p : Pattern) (guard : d5855 p = 1) : d2517 p ≤ (0 : Int) + d3237 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2517, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d2517, d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2517, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d2517, d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23389 (p : Pattern) (guard : d5855 p = 1) : d2504 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23368 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23366 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23390 (p : Pattern) (guard : d5855 p = 1) : d2518 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23389 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23391 (p : Pattern) (guard : d5855 p = 1) : d2519 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2519, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d2519, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2519, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d2519, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23392 (p : Pattern) (guard : d5851 p = 1) : d2520 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17661 p hg
    simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18648 p hg
    simpa only [d5851, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23393 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare23394 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23393 p hg
    simpa only [d5847, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d18, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23395 (p : Pattern) (guard : d5854 p = 1) : d2520 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18648 p hg
    simpa only [d5854, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23396 (p : Pattern) (guard : d5855 p = 1) : d2520 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23392 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23395 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23397 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23398 (p : Pattern) (guard : d5843 p = 1) : d1794 p ≤ (0 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23397 p hg
    simpa only [d5843, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23399 (p : Pattern) (guard : d5847 p = 1) : d1795 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1795, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d5847, d1795, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1795, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d1795, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23400 (p : Pattern) (guard : d5854 p = 1) : d2521 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23399 p hg
    simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18648 p hg
    simpa only [d5854, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23401 (p : Pattern) (guard : d5855 p = 1) : d2522 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23392 p hg
    simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23400 p hg
    simpa only [d5855, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23402 (p : Pattern) (guard : d5855 p = 1) : d2523 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23396 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23401 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23403 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23404 (p : Pattern) (guard : d5843 p = 1) : d1693 p ≤ (0 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23403 p hg
    simpa only [d5843, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23405 (p : Pattern) (guard : d5847 p = 1) : d1694 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1694, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23404 p hg
    simpa only [d5847, d1694, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1694, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d1694, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23406 (p : Pattern) (guard : d5854 p = 1) : d2524 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23405 p hg
    simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18648 p hg
    simpa only [d5854, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23407 (p : Pattern) (guard : d5855 p = 1) : d2525 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23392 p hg
    simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23406 p hg
    simpa only [d5855, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23408 (p : Pattern) (guard : d5855 p = 1) : d2526 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2526, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23407 p hg
    simpa only [d2526, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2526, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2526, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23409 (p : Pattern) (guard : d5855 p = 1) : d2527 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2527, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23402 p hg
    simpa only [d2527, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2527, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23408 p hg
    simpa only [d2527, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23410 (p : Pattern) (guard : d5855 p = 1) : d2528 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2528, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23391 p hg
    simpa only [d2528, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2528, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23409 p hg
    simpa only [d2528, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23411 (p : Pattern) (guard : d5855 p = 1) : d2529 p ≤ (0 : Int) + d3243 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2529, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23388 p hg
    simpa only [d2529, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2529, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23410 p hg
    simpa only [d2529, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23412 (p : Pattern) (guard : d5851 p = 1) : d2530 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17667 p hg
    simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18656 p hg
    simpa only [d5851, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23413 (p : Pattern) (guard : d5843 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare23414 (p : Pattern) (guard : d5847 p = 1) : d24 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23413 p hg
    simpa only [d5847, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d24, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23415 (p : Pattern) (guard : d5854 p = 1) : d2530 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23414 p hg
    simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18656 p hg
    simpa only [d5854, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23416 (p : Pattern) (guard : d5855 p = 1) : d2530 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23412 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23415 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23417 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23418 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (0 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23419 (p : Pattern) (guard : d5847 p = 1) : d356 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d5847, d356, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d356, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23420 (p : Pattern) (guard : d5854 p = 1) : d357 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23419 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18656 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23421 (p : Pattern) (guard : d5855 p = 1) : d2531 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23412 p hg
    simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23420 p hg
    simpa only [d5855, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23422 (p : Pattern) (guard : d5855 p = 1) : d2532 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23416 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23421 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23423 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23424 (p : Pattern) (guard : d5843 p = 1) : d1701 p ≤ (0 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23423 p hg
    simpa only [d5843, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23425 (p : Pattern) (guard : d5847 p = 1) : d1702 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1702, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23424 p hg
    simpa only [d5847, d1702, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1702, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d1702, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23426 (p : Pattern) (guard : d5854 p = 1) : d2533 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23425 p hg
    simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18656 p hg
    simpa only [d5854, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23427 (p : Pattern) (guard : d5855 p = 1) : d2534 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23412 p hg
    simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23426 p hg
    simpa only [d5855, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23428 (p : Pattern) (guard : d5855 p = 1) : d2535 p ≤ (0 : Int) + d3245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2535, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23427 p hg
    simpa only [d2535, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2535, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2535, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23429 (p : Pattern) (guard : d5855 p = 1) : d2536 p ≤ (0 : Int) + d3246 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2536, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23422 p hg
    simpa only [d2536, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2536, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23428 p hg
    simpa only [d2536, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23430 (p : Pattern) (guard : d5855 p = 1) : d2537 p ≤ (0 : Int) + d3247 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2537, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23429 p hg
    simpa only [d2537, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2537, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2537, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23431 (p : Pattern) (guard : d5855 p = 1) : d2538 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2538, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23410 p hg
    simpa only [d2538, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2538, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23430 p hg
    simpa only [d2538, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23432 (p : Pattern) (guard : d5855 p = 1) : d2539 p ≤ (0 : Int) + d3249 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2539, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23411 p hg
    simpa only [d2539, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2539, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23431 p hg
    simpa only [d2539, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23433 (p : Pattern) (guard : d5851 p = 1) : d2540 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18663 p hg
    simpa only [d5851, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23434 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23435 (p : Pattern) (guard : d5843 p = 1) : d1713 p ≤ (0 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23434 p hg
    simpa only [d5843, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23436 (p : Pattern) (guard : d5847 p = 1) : d1714 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1714, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23435 p hg
    simpa only [d5847, d1714, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1714, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d1714, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23437 (p : Pattern) (guard : d5854 p = 1) : d2541 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23436 p hg
    simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18663 p hg
    simpa only [d5854, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23438 (p : Pattern) (guard : d5855 p = 1) : d2542 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23433 p hg
    simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23437 p hg
    simpa only [d5855, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23439 (p : Pattern) (guard : d5855 p = 1) : d2543 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2543, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23438 p hg
    simpa only [d2543, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2543, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2543, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23440 (p : Pattern) (guard : d5855 p = 1) : d2544 p ≤ (0 : Int) + d3252 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2544, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d2544, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2544, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23439 p hg
    simpa only [d2544, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23441 (p : Pattern) (guard : d5851 p = 1) : d2545 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17678 p hg
    simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18667 p hg
    simpa only [d5851, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23442 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23443 (p : Pattern) (guard : d5843 p = 1) : d1721 p ≤ (0 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23442 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23444 (p : Pattern) (guard : d5847 p = 1) : d1722 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1722, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23443 p hg
    simpa only [d5847, d1722, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1722, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d1722, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23445 (p : Pattern) (guard : d5854 p = 1) : d2546 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23444 p hg
    simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18667 p hg
    simpa only [d5854, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23446 (p : Pattern) (guard : d5855 p = 1) : d2547 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23441 p hg
    simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23445 p hg
    simpa only [d5855, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23447 (p : Pattern) (guard : d5855 p = 1) : d2548 p ≤ (0 : Int) + d3254 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2548, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23446 p hg
    simpa only [d2548, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2548, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2548, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23448 (p : Pattern) (guard : d5855 p = 1) : d2549 p ≤ (0 : Int) + d3255 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2549, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d2549, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2549, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23447 p hg
    simpa only [d2549, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23449 (p : Pattern) (guard : d5855 p = 1) : d2550 p ≤ (0 : Int) + d3256 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2550, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23440 p hg
    simpa only [d2550, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2550, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23448 p hg
    simpa only [d2550, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23450 (p : Pattern) (guard : d5851 p = 1) : d2551 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17683 p hg
    simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18672 p hg
    simpa only [d5851, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23451 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23452 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (0 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23453 (p : Pattern) (guard : d5847 p = 1) : d327 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d5847, d327, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d327, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23454 (p : Pattern) (guard : d5854 p = 1) : d332 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23453 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18672 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23455 (p : Pattern) (guard : d5855 p = 1) : d2552 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23450 p hg
    simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23454 p hg
    simpa only [d5855, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23456 (p : Pattern) (guard : d5855 p = 1) : d2553 p ≤ (0 : Int) + d3258 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2553, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23455 p hg
    simpa only [d2553, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2553, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2553, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23457 (p : Pattern) (guard : d5855 p = 1) : d2554 p ≤ (0 : Int) + d3259 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2554, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d2554, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2554, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23456 p hg
    simpa only [d2554, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23458 (p : Pattern) (guard : d5855 p = 1) : d2555 p ≤ (0 : Int) + d3260 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2555, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23402 p hg
    simpa only [d2555, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2555, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2555, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23459 (p : Pattern) (guard : d5855 p = 1) : d2556 p ≤ (0 : Int) + d3261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2556, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23457 p hg
    simpa only [d2556, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2556, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23458 p hg
    simpa only [d2556, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23460 (p : Pattern) (guard : d5855 p = 1) : d2557 p ≤ (0 : Int) + d3262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2557, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23449 p hg
    simpa only [d2557, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2557, d3262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23459 p hg
    simpa only [d2557, d3262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23461 (p : Pattern) (guard : d5855 p = 1) : d2558 p ≤ (0 : Int) + d3263 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2558, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d2558, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2558, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2558, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23462 (p : Pattern) (guard : d5855 p = 1) : d2559 p ≤ (0 : Int) + d3264 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2559, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23461 p hg
    simpa only [d2559, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2559, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23458 p hg
    simpa only [d2559, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23463 (p : Pattern) (guard : d5855 p = 1) : d2560 p ≤ (0 : Int) + d3265 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2560, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23422 p hg
    simpa only [d2560, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2560, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2560, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23464 (p : Pattern) (guard : d5855 p = 1) : d2561 p ≤ (0 : Int) + d3266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2561, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23463 p hg
    simpa only [d2561, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2561, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2561, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23465 (p : Pattern) (guard : d5855 p = 1) : d2562 p ≤ (0 : Int) + d3267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2562, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23462 p hg
    simpa only [d2562, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2562, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23464 p hg
    simpa only [d2562, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23466 (p : Pattern) (guard : d5855 p = 1) : d2563 p ≤ (0 : Int) + d3268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2563, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23460 p hg
    simpa only [d2563, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2563, d3268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23465 p hg
    simpa only [d2563, d3268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23467 (p : Pattern) (guard : d5855 p = 1) : d2564 p ≤ (0 : Int) + d3269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2564, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23432 p hg
    simpa only [d2564, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2564, d3269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23466 p hg
    simpa only [d2564, d3269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23468 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23469 (p : Pattern) (guard : d5851 p = 1) : d2565 p ≤ (0 : Int) + d3271 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2565, d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17697 p hg
    simpa only [d5851, d2565, d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2565, d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23468 p hg
    simpa only [d5851, d2565, d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23470 (p : Pattern) (guard : d5855 p = 1) : d2566 p ≤ (0 : Int) + d3272 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2566, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23469 p hg
    simpa only [d5855, d2566, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2566, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23366 p hg
    simpa only [d5855, d2566, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23471 (p : Pattern) (guard : d5855 p = 1) : d2567 p ≤ (0 : Int) + d3273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2567, d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23470 p hg
    simpa only [d2567, d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2567, d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d2567, d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23472 (p : Pattern) (guard : d5855 p = 1) : d2568 p ≤ (0 : Int) + d3274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2568, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23471 p hg
    simpa only [d2568, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2568, d3274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d2568, d3274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23473 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare23474 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23473 p hg
    simpa only [d5847, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d31, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23475 (p : Pattern) (guard : d5854 p = 1) : d2540 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23474 p hg
    simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18663 p hg
    simpa only [d5854, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23476 (p : Pattern) (guard : d5855 p = 1) : d2540 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23433 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23475 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23477 (p : Pattern) (guard : d5855 p = 1) : d2569 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23476 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23438 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23478 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23479 (p : Pattern) (guard : d5843 p = 1) : d1742 p ≤ (0 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23478 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23480 (p : Pattern) (guard : d5847 p = 1) : d1743 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1743, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23479 p hg
    simpa only [d5847, d1743, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1743, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d1743, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23481 (p : Pattern) (guard : d5854 p = 1) : d2570 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23480 p hg
    simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18663 p hg
    simpa only [d5854, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23482 (p : Pattern) (guard : d5855 p = 1) : d2571 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23433 p hg
    simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23481 p hg
    simpa only [d5855, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23483 (p : Pattern) (guard : d5855 p = 1) : d2572 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2572, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23482 p hg
    simpa only [d2572, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2572, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2572, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23484 (p : Pattern) (guard : d5855 p = 1) : d2573 p ≤ (0 : Int) + d3275 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2573, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23477 p hg
    simpa only [d2573, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2573, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23483 p hg
    simpa only [d2573, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23485 (p : Pattern) (guard : d5855 p = 1) : d2574 p ≤ (0 : Int) + d3276 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2574, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23472 p hg
    simpa only [d2574, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2574, d3276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23484 p hg
    simpa only [d2574, d3276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23486 (p : Pattern) (guard : d5855 p = 1) : d2575 p ≤ (0 : Int) + d3277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2575, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23409 p hg
    simpa only [d2575, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2575, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23429 p hg
    simpa only [d2575, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23487 (p : Pattern) (guard : d5855 p = 1) : d2576 p ≤ (0 : Int) + d3278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2576, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23485 p hg
    simpa only [d2576, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2576, d3278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23486 p hg
    simpa only [d2576, d3278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23488 (p : Pattern) (guard : d5851 p = 1) : d2577 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17707 p hg
    simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18694 p hg
    simpa only [d5851, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23489 (p : Pattern) (guard : d5843 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  omega
theorem compare23490 (p : Pattern) (guard : d5847 p = 1) : d58 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23489 p hg
    simpa only [d5847, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23491 (p : Pattern) (guard : d5854 p = 1) : d2577 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23490 p hg
    simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18694 p hg
    simpa only [d5854, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23492 (p : Pattern) (guard : d5855 p = 1) : d2577 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23488 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23491 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23493 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23494 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (0 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23495 (p : Pattern) (guard : d5847 p = 1) : d329 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d5847, d329, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d329, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23496 (p : Pattern) (guard : d5854 p = 1) : d330 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23495 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18694 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23497 (p : Pattern) (guard : d5855 p = 1) : d2578 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23488 p hg
    simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23496 p hg
    simpa only [d5855, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23498 (p : Pattern) (guard : d5855 p = 1) : d2579 p ≤ (0 : Int) + d3279 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23492 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23497 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23499 (p : Pattern) (guard : d5855 p = 1) : d2580 p ≤ (0 : Int) + d3280 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2580, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23497 p hg
    simpa only [d2580, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2580, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2580, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23500 (p : Pattern) (guard : d5855 p = 1) : d2581 p ≤ (0 : Int) + d3281 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2581, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23498 p hg
    simpa only [d2581, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2581, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23499 p hg
    simpa only [d2581, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23501 (p : Pattern) (guard : d5855 p = 1) : d2582 p ≤ (0 : Int) + d3282 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2582, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23409 p hg
    simpa only [d2582, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2582, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23500 p hg
    simpa only [d2582, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23502 (p : Pattern) (guard : d5843 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare23503 (p : Pattern) (guard : d5847 p = 1) : d40 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23502 p hg
    simpa only [d5847, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23504 (p : Pattern) (guard : d5854 p = 1) : d2551 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23503 p hg
    simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18672 p hg
    simpa only [d5854, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23505 (p : Pattern) (guard : d5855 p = 1) : d2551 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23450 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23504 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23506 (p : Pattern) (guard : d5855 p = 1) : d2583 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23505 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23455 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23507 (p : Pattern) (guard : d5855 p = 1) : d2584 p ≤ (0 : Int) + d3283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2584, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23506 p hg
    simpa only [d2584, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2584, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23456 p hg
    simpa only [d2584, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23508 (p : Pattern) (guard : d5855 p = 1) : d2585 p ≤ (0 : Int) + d3284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2585, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2585, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2585, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2585, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23509 (p : Pattern) (guard : d5855 p = 1) : d2586 p ≤ (0 : Int) + d3285 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2586, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23501 p hg
    simpa only [d2586, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2586, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23508 p hg
    simpa only [d2586, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23510 (p : Pattern) (guard : d5855 p = 1) : d2587 p ≤ (0 : Int) + d3286 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2587, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23487 p hg
    simpa only [d2587, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2587, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23509 p hg
    simpa only [d2587, d3286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23511 (p : Pattern) (guard : d5855 p = 1) : d2588 p ≤ (0 : Int) + d3287 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2588, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23477 p hg
    simpa only [d2588, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2588, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2588, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23512 (p : Pattern) (guard : d5855 p = 1) : d2589 p ≤ (0 : Int) + d3288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2589, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23448 p hg
    simpa only [d2589, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2589, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23511 p hg
    simpa only [d2589, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23513 (p : Pattern) (guard : d5855 p = 1) : d2590 p ≤ (0 : Int) + d3289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2590, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23458 p hg
    simpa only [d2590, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2590, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23463 p hg
    simpa only [d2590, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23514 (p : Pattern) (guard : d5855 p = 1) : d2591 p ≤ (0 : Int) + d3290 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2591, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23512 p hg
    simpa only [d2591, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2591, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23513 p hg
    simpa only [d2591, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23515 (p : Pattern) (guard : d5855 p = 1) : d2592 p ≤ (0 : Int) + d3291 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2592, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23498 p hg
    simpa only [d2592, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2592, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2592, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23516 (p : Pattern) (guard : d5855 p = 1) : d2593 p ≤ (0 : Int) + d3292 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2593, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23458 p hg
    simpa only [d2593, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2593, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23515 p hg
    simpa only [d2593, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23517 (p : Pattern) (guard : d5855 p = 1) : d2594 p ≤ (0 : Int) + d3293 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2594, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23506 p hg
    simpa only [d2594, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2594, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2594, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23518 (p : Pattern) (guard : d5855 p = 1) : d2595 p ≤ (0 : Int) + d3294 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2595, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23517 p hg
    simpa only [d2595, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2595, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2595, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23519 (p : Pattern) (guard : d5855 p = 1) : d2596 p ≤ (0 : Int) + d3295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2596, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23516 p hg
    simpa only [d2596, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2596, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23518 p hg
    simpa only [d2596, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
