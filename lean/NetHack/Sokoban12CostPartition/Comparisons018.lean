/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2520 (p : Pattern) (guard : d1014 p = 1) : d74 p ≤ (2 : Int) + d842 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2519 p hg
    simpa only [d74, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2521 (p : Pattern) (guard : d1014 p = 1) : d236 p ≤ (2 : Int) + d843 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d236, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d236, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d236, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2520 p hg
    simpa only [d236, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2522 (p : Pattern) (guard : d1053 p = 1) : d56 p ≤ (0 : Int) + d56 p := by
  omega
theorem compare2523 (p : Pattern) (guard : d1054 p = 1) : d57 p ≤ (0 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2522 p hg
    simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2524 (p : Pattern) (guard : d1053 p = 1) : d62 p ≤ (0 : Int) + d62 p := by
  omega
theorem compare2525 (p : Pattern) (guard : d1054 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2526 (p : Pattern) (guard : d1054 p = 1) : d64 p ≤ (0 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2527 (p : Pattern) (guard : d1053 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2528 (p : Pattern) (guard : d1054 p = 1) : d106 p ≤ (0 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1054, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d1054, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2529 (p : Pattern) (guard : d1053 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2530 (p : Pattern) (guard : d1054 p = 1) : d109 p ≤ (0 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d1054, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d1054, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2531 (p : Pattern) (guard : d1054 p = 1) : d227 p ≤ (0 : Int) + d454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2532 (p : Pattern) (guard : d1054 p = 1) : d228 p ≤ (0 : Int) + d455 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d228, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d228, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d228, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2531 p hg
    simpa only [d228, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2533 (p : Pattern) (guard : d1054 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2534 (p : Pattern) (guard : d1054 p = 1) : d68 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2535 (p : Pattern) (guard : d1054 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2536 (p : Pattern) (guard : d1054 p = 1) : d69 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2537 (p : Pattern) (guard : d1054 p = 1) : d70 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2536 p hg
    simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2538 (p : Pattern) (guard : d1054 p = 1) : d229 p ≤ (0 : Int) + d459 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2539 (p : Pattern) (guard : d1054 p = 1) : d230 p ≤ (0 : Int) + d460 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2540 (p : Pattern) (guard : d1054 p = 1) : d231 p ≤ (0 : Int) + d461 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2538 p hg
    simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2539 p hg
    simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2541 (p : Pattern) (guard : d1054 p = 1) : d232 p ≤ (0 : Int) + d462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d232, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2537 p hg
    simpa only [d232, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d232, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2540 p hg
    simpa only [d232, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2542 (p : Pattern) (guard : d1054 p = 1) : d233 p ≤ (0 : Int) + d463 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d233, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2532 p hg
    simpa only [d233, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d233, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2541 p hg
    simpa only [d233, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2543 (p : Pattern) (guard : d1054 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2544 (p : Pattern) (guard : d1054 p = 1) : d234 p ≤ (0 : Int) + d464 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d234, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2541 p hg
    simpa only [d234, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d234, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d234, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2545 (p : Pattern) (guard : d1054 p = 1) : d235 p ≤ (0 : Int) + d465 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d235, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d235, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d235, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2544 p hg
    simpa only [d235, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2546 (p : Pattern) (guard : d1053 p = 1) : d56 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1053, d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1053, d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2547 (p : Pattern) (guard : d1054 p = 1) : d57 p ≤ (0 : Int) + d466 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d57, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1054, d57, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d57, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2546 p hg
    simpa only [d1054, d57, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2548 (p : Pattern) (guard : d1054 p = 1) : d57 p ≤ (0 : Int) + d467 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2547 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2549 (p : Pattern) (guard : d1054 p = 1) : d57 p ≤ (0 : Int) + d468 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2548 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2550 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2551 (p : Pattern) (guard : d1053 p = 1) : d61 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d1053, d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d1053, d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2552 (p : Pattern) (guard : d1053 p = 1) : d62 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2546 p hg
    simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2551 p hg
    simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2553 (p : Pattern) (guard : d1054 p = 1) : d63 p ≤ (0 : Int) + d469 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d63, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d1054, d63, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d63, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d1054, d63, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2554 (p : Pattern) (guard : d1054 p = 1) : d63 p ≤ (0 : Int) + d470 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2553 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2555 (p : Pattern) (guard : d1054 p = 1) : d63 p ≤ (0 : Int) + d471 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2554 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2556 (p : Pattern) (guard : d1054 p = 1) : d64 p ≤ (0 : Int) + d472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d64, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2549 p hg
    simpa only [d64, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d64, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2555 p hg
    simpa only [d64, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2557 (p : Pattern) (guard : d1054 p = 1) : d67 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d67, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d67, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d67, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d67, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2558 (p : Pattern) (guard : d1054 p = 1) : d68 p ≤ (0 : Int) + d474 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d68, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2547 p hg
    simpa only [d68, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d68, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d68, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2559 (p : Pattern) (guard : d1054 p = 1) : d69 p ≤ (0 : Int) + d475 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d69, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2553 p hg
    simpa only [d69, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d69, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d69, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2560 (p : Pattern) (guard : d1054 p = 1) : d70 p ≤ (0 : Int) + d476 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d70, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2558 p hg
    simpa only [d70, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d70, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d70, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2561 (p : Pattern) (guard : d1054 p = 1) : d71 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d71, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2560 p hg
    simpa only [d71, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d71, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d71, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2562 (p : Pattern) (guard : d1054 p = 1) : d72 p ≤ (0 : Int) + d478 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d72, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d72, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d72, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d72, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2563 (p : Pattern) (guard : d1054 p = 1) : d68 p ≤ (0 : Int) + d479 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d68, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2548 p hg
    simpa only [d68, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d68, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d68, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2564 (p : Pattern) (guard : d1054 p = 1) : d69 p ≤ (0 : Int) + d480 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d69, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2554 p hg
    simpa only [d69, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d69, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d69, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2565 (p : Pattern) (guard : d1054 p = 1) : d70 p ≤ (0 : Int) + d481 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d70, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2563 p hg
    simpa only [d70, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d70, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2564 p hg
    simpa only [d70, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2566 (p : Pattern) (guard : d1054 p = 1) : d71 p ≤ (0 : Int) + d482 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d71, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d71, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d71, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d71, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2567 (p : Pattern) (guard : d1054 p = 1) : d73 p ≤ (0 : Int) + d483 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d73, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2566 p hg
    simpa only [d73, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d73, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d73, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2568 (p : Pattern) (guard : d1054 p = 1) : d74 p ≤ (0 : Int) + d484 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d74, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d74, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d74, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2567 p hg
    simpa only [d74, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2569 (p : Pattern) (guard : d1054 p = 1) : d236 p ≤ (0 : Int) + d485 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d236, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2545 p hg
    simpa only [d236, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d236, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2568 p hg
    simpa only [d236, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2570 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (2 : Int) + d258 p := by
  omega
theorem compare2571 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2572 (p : Pattern) (guard : d854 p = 1) : d7 p ≤ (0 : Int) + d24 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d7, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d854, d7, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d7, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2571 p hg
    simpa only [d854, d7, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2573 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2574 (p : Pattern) (guard : d854 p = 1) : d55 p ≤ (0 : Int) + d525 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d55, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d854, d55, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d55, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2573 p hg
    simpa only [d854, d55, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2575 (p : Pattern) (guard : d854 p = 1) : d56 p ≤ (0 : Int) + d526 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d56, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d56, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d56, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d56, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2576 (p : Pattern) (guard : d854 p = 1) : d57 p ≤ (0 : Int) + d527 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d57, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d57, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d57, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2575 p hg
    simpa only [d57, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2577 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2578 (p : Pattern) (guard : d854 p = 1) : d11 p ≤ (0 : Int) + d25 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d11, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d854, d11, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d11, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2577 p hg
    simpa only [d854, d11, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2579 (p : Pattern) (guard : d854 p = 1) : d12 p ≤ (0 : Int) + d26 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d12, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d12, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d12, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d12, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2580 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2581 (p : Pattern) (guard : d854 p = 1) : d60 p ≤ (0 : Int) + d528 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d60, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d854, d60, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d60, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2580 p hg
    simpa only [d854, d60, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2582 (p : Pattern) (guard : d854 p = 1) : d61 p ≤ (0 : Int) + d529 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d61, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d61, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d61, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d61, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2583 (p : Pattern) (guard : d854 p = 1) : d62 p ≤ (0 : Int) + d530 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d62, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2575 p hg
    simpa only [d62, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d62, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d62, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2584 (p : Pattern) (guard : d854 p = 1) : d63 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d63, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2579 p hg
    simpa only [d63, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d63, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2583 p hg
    simpa only [d63, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2585 (p : Pattern) (guard : d854 p = 1) : d64 p ≤ (0 : Int) + d532 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d64, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d64, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d64, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d64, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2586 (p : Pattern) (guard : d854 p = 1) : d106 p ≤ (0 : Int) + d533 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d106, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d106, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d106, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d106, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2587 (p : Pattern) (guard : d854 p = 1) : d119 p ≤ (0 : Int) + d534 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d119, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d119, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d119, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d119, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2588 (p : Pattern) (guard : d854 p = 1) : d120 p ≤ (0 : Int) + d535 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d120, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d120, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d120, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2587 p hg
    simpa only [d120, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2589 (p : Pattern) (guard : d854 p = 1) : d121 p ≤ (0 : Int) + d536 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d121, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2588 p hg
    simpa only [d121, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d121, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d121, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2590 (p : Pattern) (guard : d854 p = 1) : d122 p ≤ (0 : Int) + d537 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d122, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2586 p hg
    simpa only [d122, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d122, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d122, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2591 (p : Pattern) (guard : d854 p = 1) : d179 p ≤ (0 : Int) + d538 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d179, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2586 p hg
    simpa only [d179, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d179, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d179, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2592 (p : Pattern) (guard : d854 p = 1) : d65 p ≤ (0 : Int) + d539 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d65, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d65, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d65, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d65, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2593 (p : Pattern) (guard : d854 p = 1) : d109 p ≤ (0 : Int) + d540 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d109, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2579 p hg
    simpa only [d109, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d109, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d109, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2594 (p : Pattern) (guard : d854 p = 1) : d125 p ≤ (0 : Int) + d541 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d125, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d125, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d125, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d125, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2595 (p : Pattern) (guard : d854 p = 1) : d126 p ≤ (0 : Int) + d542 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d126, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d126, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d126, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d126, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2596 (p : Pattern) (guard : d854 p = 1) : d127 p ≤ (0 : Int) + d543 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d127, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2588 p hg
    simpa only [d127, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d127, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2595 p hg
    simpa only [d127, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2597 (p : Pattern) (guard : d854 p = 1) : d128 p ≤ (0 : Int) + d544 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d128, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d128, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d128, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d128, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2598 (p : Pattern) (guard : d854 p = 1) : d129 p ≤ (0 : Int) + d545 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d129, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d129, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d129, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d129, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2599 (p : Pattern) (guard : d854 p = 1) : d237 p ≤ (0 : Int) + d546 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d237, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d237, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d237, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2598 p hg
    simpa only [d237, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2600 (p : Pattern) (guard : d854 p = 1) : d238 p ≤ (0 : Int) + d547 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d238, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2591 p hg
    simpa only [d238, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d238, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2599 p hg
    simpa only [d238, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2601 (p : Pattern) (guard : d854 p = 1) : d239 p ≤ (0 : Int) + d548 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d239, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2585 p hg
    simpa only [d239, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d239, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2600 p hg
    simpa only [d239, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2602 (p : Pattern) (guard : d854 p = 1) : d68 p ≤ (0 : Int) + d549 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d68, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d68, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d68, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d68, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2603 (p : Pattern) (guard : d854 p = 1) : d69 p ≤ (0 : Int) + d550 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d69, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d69, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d69, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d69, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2604 (p : Pattern) (guard : d854 p = 1) : d70 p ≤ (0 : Int) + d551 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d70, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d70, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d70, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2603 p hg
    simpa only [d70, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2605 (p : Pattern) (guard : d854 p = 1) : d181 p ≤ (0 : Int) + d552 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d181, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d181, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d181, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d181, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2606 (p : Pattern) (guard : d854 p = 1) : d240 p ≤ (0 : Int) + d553 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d240, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2598 p hg
    simpa only [d240, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d240, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d240, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2607 (p : Pattern) (guard : d854 p = 1) : d241 p ≤ (0 : Int) + d554 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d241, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2605 p hg
    simpa only [d241, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d241, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d241, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2608 (p : Pattern) (guard : d854 p = 1) : d242 p ≤ (0 : Int) + d555 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d242, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2604 p hg
    simpa only [d242, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d242, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2607 p hg
    simpa only [d242, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2609 (p : Pattern) (guard : d854 p = 1) : d243 p ≤ (0 : Int) + d556 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d243, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d243, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d243, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2608 p hg
    simpa only [d243, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2610 (p : Pattern) (guard : d854 p = 1) : d66 p ≤ (0 : Int) + d557 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d66, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d66, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d66, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d66, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2611 (p : Pattern) (guard : d854 p = 1) : d244 p ≤ (0 : Int) + d558 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d244, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2608 p hg
    simpa only [d244, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d244, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d244, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2612 (p : Pattern) (guard : d854 p = 1) : d245 p ≤ (0 : Int) + d559 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d245, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d245, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d245, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d245, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2613 (p : Pattern) (guard : d854 p = 1) : d137 p ≤ (0 : Int) + d560 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d137, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2587 p hg
    simpa only [d137, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d137, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d137, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2614 (p : Pattern) (guard : d854 p = 1) : d139 p ≤ (0 : Int) + d561 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d139, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2588 p hg
    simpa only [d139, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d139, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2613 p hg
    simpa only [d139, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2615 (p : Pattern) (guard : d854 p = 1) : d153 p ≤ (0 : Int) + d562 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d153, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d153, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d153, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2614 p hg
    simpa only [d153, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2616 (p : Pattern) (guard : d854 p = 1) : d186 p ≤ (0 : Int) + d563 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d186, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d186, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d186, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2615 p hg
    simpa only [d186, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2617 (p : Pattern) (guard : d854 p = 1) : d143 p ≤ (0 : Int) + d564 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d143, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d143, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d143, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d143, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2618 (p : Pattern) (guard : d854 p = 1) : d144 p ≤ (0 : Int) + d565 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d144, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2613 p hg
    simpa only [d144, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d144, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d144, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2619 (p : Pattern) (guard : d854 p = 1) : d146 p ≤ (0 : Int) + d566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d146, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d146, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d146, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2618 p hg
    simpa only [d146, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2620 (p : Pattern) (guard : d854 p = 1) : d155 p ≤ (0 : Int) + d567 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d155, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d155, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d155, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d155, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2621 (p : Pattern) (guard : d854 p = 1) : d246 p ≤ (0 : Int) + d568 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d246, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d246, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d246, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2620 p hg
    simpa only [d246, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2622 (p : Pattern) (guard : d854 p = 1) : d247 p ≤ (0 : Int) + d569 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d247, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2616 p hg
    simpa only [d247, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d247, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d247, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2623 (p : Pattern) (guard : d854 p = 1) : d248 p ≤ (0 : Int) + d570 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d248, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2622 p hg
    simpa only [d248, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d248, d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d248, d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2624 (p : Pattern) (guard : d854 p = 1) : d138 p ≤ (0 : Int) + d571 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d138, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d138, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d138, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2613 p hg
    simpa only [d138, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2625 (p : Pattern) (guard : d854 p = 1) : d140 p ≤ (0 : Int) + d572 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d140, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2624 p hg
    simpa only [d140, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d140, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2614 p hg
    simpa only [d140, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2626 (p : Pattern) (guard : d854 p = 1) : d188 p ≤ (0 : Int) + d573 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d188, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2625 p hg
    simpa only [d188, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d188, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d188, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2627 (p : Pattern) (guard : d854 p = 1) : d145 p ≤ (0 : Int) + d574 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d145, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2579 p hg
    simpa only [d145, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d145, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2618 p hg
    simpa only [d145, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2628 (p : Pattern) (guard : d854 p = 1) : d147 p ≤ (0 : Int) + d575 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d147, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2627 p hg
    simpa only [d147, d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d147, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d147, d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2629 (p : Pattern) (guard : d854 p = 1) : d249 p ≤ (0 : Int) + d576 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d249, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2628 p hg
    simpa only [d249, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d249, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d249, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2630 (p : Pattern) (guard : d854 p = 1) : d250 p ≤ (0 : Int) + d577 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d250, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2626 p hg
    simpa only [d250, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d250, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2629 p hg
    simpa only [d250, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2631 (p : Pattern) (guard : d854 p = 1) : d251 p ≤ (0 : Int) + d578 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d251, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2630 p hg
    simpa only [d251, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d251, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d251, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2632 (p : Pattern) (guard : d854 p = 1) : d252 p ≤ (0 : Int) + d579 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d252, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2623 p hg
    simpa only [d252, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d252, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2631 p hg
    simpa only [d252, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2633 (p : Pattern) (guard : d854 p = 1) : d191 p ≤ (0 : Int) + d580 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d191, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2615 p hg
    simpa only [d191, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d191, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d191, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2634 (p : Pattern) (guard : d854 p = 1) : d253 p ≤ (0 : Int) + d581 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d253, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2620 p hg
    simpa only [d253, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d253, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d253, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2635 (p : Pattern) (guard : d854 p = 1) : d254 p ≤ (0 : Int) + d582 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d254, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2633 p hg
    simpa only [d254, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d254, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2634 p hg
    simpa only [d254, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2636 (p : Pattern) (guard : d854 p = 1) : d255 p ≤ (0 : Int) + d583 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d255, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2635 p hg
    simpa only [d255, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d255, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d255, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2637 (p : Pattern) (guard : d854 p = 1) : d256 p ≤ (0 : Int) + d584 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d256, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2636 p hg
    simpa only [d256, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d256, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d256, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2638 (p : Pattern) (guard : d854 p = 1) : d257 p ≤ (0 : Int) + d585 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d257, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2632 p hg
    simpa only [d257, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d257, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2637 p hg
    simpa only [d257, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2639 (p : Pattern) (guard : d854 p = 1) : d258 p ≤ (0 : Int) + d586 p := by
  cases selected : p 108 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d258, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2612 p hg
    simpa only [d258, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d258, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2638 p hg
    simpa only [d258, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2640 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2641 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare2642 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2643 (p : Pattern) (guard : d853 p = 1) : d7 p ≤ (2 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d853, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d853, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d853, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2642 p hg
    simpa only [d853, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2644 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2645 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare2646 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (2 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2647 (p : Pattern) (guard : d853 p = 1) : d55 p ≤ (2 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d853, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d853, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d853, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d853, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2648 (p : Pattern) (guard : d853 p = 1) : d56 p ≤ (2 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2649 (p : Pattern) (guard : d853 p = 1) : d57 p ≤ (2 : Int) + d46 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2650 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2651 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  omega
theorem compare2652 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d8 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2653 (p : Pattern) (guard : d853 p = 1) : d11 p ≤ (2 : Int) + d8 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d853, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d853, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d853, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2652 p hg
    simpa only [d853, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2654 (p : Pattern) (guard : d853 p = 1) : d12 p ≤ (2 : Int) + d1055 p := by
  cases selected : p 168 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2655 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2656 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  omega
theorem compare2657 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare86 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2658 (p : Pattern) (guard : d853 p = 1) : d60 p ≤ (2 : Int) + d9 p := by
  cases selected : p 192 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d853, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d853, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d853, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2657 p hg
    simpa only [d853, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2659 (p : Pattern) (guard : d853 p = 1) : d61 p ≤ (2 : Int) + d1056 p := by
  cases selected : p 186 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
