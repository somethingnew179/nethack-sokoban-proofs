import NetHack.Soko22Hazard87.Compare009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2500 (p : Pattern) (guard : d34 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2498 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2501 (p : Pattern) (guard : d35 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2500 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2502 (p : Pattern) (guard : d36 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2501 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2503 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (0 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2504 (p : Pattern) (guard : d37 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2502 p hg
    simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d37, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2505 (p : Pattern) (guard : d38 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2504 p hg
    simpa only [d38, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2506 (p : Pattern) (guard : d39 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2505 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2507 (p : Pattern) (guard : d40 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2506 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2508 (p : Pattern) (guard : d41 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2509 (p : Pattern) (guard : d42 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2510 (p : Pattern) (guard : d43 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2511 (p : Pattern) (guard : d44 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d43 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2512 (p : Pattern) (guard : d45 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d44 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2513 (p : Pattern) (guard : d46 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2514 (p : Pattern) (guard : d47 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2515 (p : Pattern) (guard : d48 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d48, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d48, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47 p = 1 := by simpa only [d48, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2514 p hg
    simpa only [d48, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2516 (p : Pattern) (guard : d47 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2517 (p : Pattern) (guard : d49 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2518 (p : Pattern) (guard : d50 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2517 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2519 (p : Pattern) (guard : d51 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2520 (p : Pattern) (guard : d52 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2519 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2521 (p : Pattern) (guard : d53 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2520 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2522 (p : Pattern) (guard : d54 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2521 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2523 (p : Pattern) (guard : d55 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d47 p = 1 := by simpa only [d55, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d55, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d55, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2522 p hg
    simpa only [d55, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2524 (p : Pattern) (guard : d56 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d48 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2525 (p : Pattern) (guard : d57 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d56 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2526 (p : Pattern) (guard : d58 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d57 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2527 (p : Pattern) (guard : d59 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d58 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2528 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2529 (p : Pattern) (guard : d2519 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d59 p = 1 := by simpa only [d2519, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d2519, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2519, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d2519, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2530 (p : Pattern) (guard : d0 p = 1) : d47910 p ≤ (0 : Int) + d47909 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2531 (p : Pattern) (guard : d2520 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d2519 p = 1 := by simpa only [d2520, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d2520, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2520, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d2520, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2532 (p : Pattern) (guard : d2521 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2520 p = 1 := by simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2531 p hg
    simpa only [d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2533 (p : Pattern) (guard : d2522 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2521 p = 1 := by simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2532 p hg
    simpa only [d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2534 (p : Pattern) (guard : d2523 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2522 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2535 (p : Pattern) (guard : d2524 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2523 p = 1 := by simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2536 (p : Pattern) (guard : d115 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d40 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2537 (p : Pattern) (guard : d116 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d115 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2536 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2538 (p : Pattern) (guard : d117 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d116 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2537 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2539 (p : Pattern) (guard : d118 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d117 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2538 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2540 (p : Pattern) (guard : d119 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d118 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2539 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2541 (p : Pattern) (guard : d120 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d119 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2540 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2542 (p : Pattern) (guard : d121 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2506 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2543 (p : Pattern) (guard : d122 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d121 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2544 (p : Pattern) (guard : d123 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d122 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2545 (p : Pattern) (guard : d124 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d123 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2544 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2546 (p : Pattern) (guard : d125 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d124 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2545 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2547 (p : Pattern) (guard : d126 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d125 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2546 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2548 (p : Pattern) (guard : d139 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d139, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2549 (p : Pattern) (guard : d140 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2548 p hg
    simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d140, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2550 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2549 p hg
    simpa only [d141, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2551 (p : Pattern) (guard : d142 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d142, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2552 (p : Pattern) (guard : d143 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2551 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2492 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2553 (p : Pattern) (guard : d144 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2554 (p : Pattern) (guard : d145 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2553 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2495 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2555 (p : Pattern) (guard : d146 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2554 p hg
    simpa only [d146, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2556 (p : Pattern) (guard : d147 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2555 p hg
    simpa only [d147, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2557 (p : Pattern) (guard : d148 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2498 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2558 (p : Pattern) (guard : d149 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2500 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2559 (p : Pattern) (guard : d150 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2558 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2560 (p : Pattern) (guard : d151 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d151, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2561 (p : Pattern) (guard : d152 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2560 p hg
    simpa only [d152, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2562 (p : Pattern) (guard : d153 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2505 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2563 (p : Pattern) (guard : d154 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2564 (p : Pattern) (guard : d155 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2563 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2565 (p : Pattern) (guard : d156 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2564 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2566 (p : Pattern) (guard : d157 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2567 (p : Pattern) (guard : d4335 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d157 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2566 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2568 (p : Pattern) (guard : d4336 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4335 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2567 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2569 (p : Pattern) (guard : d51641 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d126 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2547 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4336 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2568 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2570 (p : Pattern) (guard : d51642 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d120 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2541 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51641 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2569 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2571 (p : Pattern) (guard : d51643 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51643, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51643, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51642 p = 1 := by simpa only [d51643, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2570 p hg
    simpa only [d51643, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2572 (p : Pattern) (guard : d51642 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2573 (p : Pattern) (guard : d194 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d115 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2536 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2574 (p : Pattern) (guard : d195 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d194 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2573 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2575 (p : Pattern) (guard : d196 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d195 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2576 (p : Pattern) (guard : d197 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d196 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2575 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2577 (p : Pattern) (guard : d198 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d197 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2578 (p : Pattern) (guard : d199 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d122 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2579 (p : Pattern) (guard : d200 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d199 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2580 (p : Pattern) (guard : d201 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d200 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2579 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2581 (p : Pattern) (guard : d202 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d201 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2580 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2582 (p : Pattern) (guard : d203 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2564 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2583 (p : Pattern) (guard : d204 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2517 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2584 (p : Pattern) (guard : d4340 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2583 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2585 (p : Pattern) (guard : d4341 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2519 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2586 (p : Pattern) (guard : d51644 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d202 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2585 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2587 (p : Pattern) (guard : d51645 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d198 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2577 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51644 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2586 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2588 (p : Pattern) (guard : d51646 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51642 p = 1 := by simpa only [d51646, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d51646, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51645 p = 1 := by simpa only [d51646, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2587 p hg
    simpa only [d51646, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2589 (p : Pattern) (guard : d51647 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51643 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2571 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51646 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2588 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2590 (p : Pattern) (guard : d213 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d213, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2591 (p : Pattern) (guard : d214 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d213 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2592 (p : Pattern) (guard : d51648 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51647 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d214 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2591 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2593 (p : Pattern) (guard : d51649 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51648 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2594 (p : Pattern) (guard : d64416 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51649 p = 1 := by simpa only [d64416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d64416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2595 (p : Pattern) (guard : d64417 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64416 p = 1 := by simpa only [d64417, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d64417, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64417, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64417, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2596 (p : Pattern) (guard : d64418 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64417 p = 1 := by simpa only [d64418, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2595 p hg
    simpa only [d64418, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64418, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64418, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2597 (p : Pattern) (guard : d64419 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64418 p = 1 := by simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d64419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2598 (p : Pattern) (guard : d64420 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64419 p = 1 := by simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d64420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2599 (p : Pattern) (guard : d64421 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64420 p = 1 := by simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2598 p hg
    simpa only [d64421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2600 (p : Pattern) (guard : d64422 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64421 p = 1 := by simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2599 p hg
    simpa only [d64422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2601 (p : Pattern) (guard : d64423 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d2524 p = 1 := by simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64422 p = 1 := by simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2600 p hg
    simpa only [d64423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2602 (p : Pattern) (guard : d295 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d154 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2563 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2603 (p : Pattern) (guard : d296 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2604 (p : Pattern) (guard : d297 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d296 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2603 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d116 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2537 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2605 (p : Pattern) (guard : d298 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d297 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2604 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2606 (p : Pattern) (guard : d299 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d298 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2605 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2607 (p : Pattern) (guard : d300 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d299 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2608 (p : Pattern) (guard : d301 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d153 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2609 (p : Pattern) (guard : d302 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d301 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2608 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2610 (p : Pattern) (guard : d303 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d302 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2611 (p : Pattern) (guard : d304 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d303 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d123 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2544 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2612 (p : Pattern) (guard : d305 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d304 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2613 (p : Pattern) (guard : d306 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d305 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2612 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2614 (p : Pattern) (guard : d319 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d319, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2615 (p : Pattern) (guard : d320 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2614 p hg
    simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d320, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2616 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2615 p hg
    simpa only [d321, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2617 (p : Pattern) (guard : d322 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2616 p hg
    simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d322, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2618 (p : Pattern) (guard : d323 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2551 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2619 (p : Pattern) (guard : d324 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2618 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d143 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2620 (p : Pattern) (guard : d325 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2553 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2621 (p : Pattern) (guard : d326 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325 p = 1 := by simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2620 p hg
    simpa only [d326, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2622 (p : Pattern) (guard : d327 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326 p = 1 := by simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d327, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2623 (p : Pattern) (guard : d328 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2622 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2624 (p : Pattern) (guard : d329 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2623 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2625 (p : Pattern) (guard : d330 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d329 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2624 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2626 (p : Pattern) (guard : d331 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d330 p = 1 := by simpa only [d331, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2625 p hg
    simpa only [d331, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d331, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d331, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2627 (p : Pattern) (guard : d332 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d332, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d332, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d331 p = 1 := by simpa only [d332, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2626 p hg
    simpa only [d332, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2628 (p : Pattern) (guard : d333 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d332 p = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2627 p hg
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2629 (p : Pattern) (guard : d334 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d333 p = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2628 p hg
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2630 (p : Pattern) (guard : d335 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d334 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2629 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2631 (p : Pattern) (guard : d336 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d335 p = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2630 p hg
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2632 (p : Pattern) (guard : d337 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d336 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2631 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d156 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2633 (p : Pattern) (guard : d4371 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d337 p = 1 := by simpa only [d4371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2632 p hg
    simpa only [d4371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2634 (p : Pattern) (guard : d370 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2635 (p : Pattern) (guard : d371 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d370 p = 1 := by simpa only [d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2634 p hg
    simpa only [d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2636 (p : Pattern) (guard : d4372 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4371 p = 1 := by simpa only [d4372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2633 p hg
    simpa only [d4372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d371 p = 1 := by simpa only [d4372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2635 p hg
    simpa only [d4372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2637 (p : Pattern) (guard : d51658 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d306 p = 1 := by simpa only [d51658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2613 p hg
    simpa only [d51658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4372 p = 1 := by simpa only [d51658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2636 p hg
    simpa only [d51658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2638 (p : Pattern) (guard : d51659 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d300 p = 1 := by simpa only [d51659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2607 p hg
    simpa only [d51659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51658 p = 1 := by simpa only [d51659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2637 p hg
    simpa only [d51659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2639 (p : Pattern) (guard : d51660 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51660, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51660, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51659 p = 1 := by simpa only [d51660, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2638 p hg
    simpa only [d51660, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2640 (p : Pattern) (guard : d51659 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2641 (p : Pattern) (guard : d376 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2642 (p : Pattern) (guard : d377 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d376 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d194 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2573 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2643 (p : Pattern) (guard : d378 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d377 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2642 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2644 (p : Pattern) (guard : d379 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d378 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2645 (p : Pattern) (guard : d380 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d379 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2646 (p : Pattern) (guard : d381 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d302 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2647 (p : Pattern) (guard : d382 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d381 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d199 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2648 (p : Pattern) (guard : d383 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d382 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2649 (p : Pattern) (guard : d384 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d383 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2650 (p : Pattern) (guard : d385 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d335 p = 1 := by simpa only [d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2630 p hg
    simpa only [d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2651 (p : Pattern) (guard : d386 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d385 p = 1 := by simpa only [d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2652 (p : Pattern) (guard : d4376 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d386 p = 1 := by simpa only [d4376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d4376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2653 (p : Pattern) (guard : d390 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2654 (p : Pattern) (guard : d391 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d390 p = 1 := by simpa only [d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2655 (p : Pattern) (guard : d4377 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4376 p = 1 := by simpa only [d4377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2652 p hg
    simpa only [d4377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d391 p = 1 := by simpa only [d4377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d4377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2656 (p : Pattern) (guard : d51661 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d384 p = 1 := by simpa only [d51661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d51661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4377 p = 1 := by simpa only [d51661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d51661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2657 (p : Pattern) (guard : d51662 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d380 p = 1 := by simpa only [d51662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d51662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51661 p = 1 := by simpa only [d51662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d51662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2658 (p : Pattern) (guard : d51663 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51659 p = 1 := by simpa only [d51663, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d51663, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51662 p = 1 := by simpa only [d51663, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2657 p hg
    simpa only [d51663, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2659 (p : Pattern) (guard : d51664 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51660 p = 1 := by simpa only [d51664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2639 p hg
    simpa only [d51664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51663 p = 1 := by simpa only [d51664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d51664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2660 (p : Pattern) (guard : d100 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2661 (p : Pattern) (guard : d101 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2660 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2662 (p : Pattern) (guard : d102 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2663 (p : Pattern) (guard : d103 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2662 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2664 (p : Pattern) (guard : d397 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d397, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d397, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d397, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2663 p hg
    simpa only [d397, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2665 (p : Pattern) (guard : d107 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2666 (p : Pattern) (guard : d108 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2665 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2667 (p : Pattern) (guard : d109 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2666 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2668 (p : Pattern) (guard : d110 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2667 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2669 (p : Pattern) (guard : d111 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d111, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2668 p hg
    simpa only [d111, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2670 (p : Pattern) (guard : d398 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d397 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2671 (p : Pattern) (guard : d51665 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51664 p = 1 := by simpa only [d51665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2659 p hg
    simpa only [d51665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d398 p = 1 := by simpa only [d51665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2670 p hg
    simpa only [d51665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2672 (p : Pattern) (guard : d51666 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51665 p = 1 := by simpa only [d51666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2671 p hg
    simpa only [d51666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2673 (p : Pattern) (guard : d64424 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51666 p = 1 := by simpa only [d64424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2672 p hg
    simpa only [d64424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2674 (p : Pattern) (guard : d64425 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64424 p = 1 := by simpa only [d64425, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2673 p hg
    simpa only [d64425, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64425, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64425, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2675 (p : Pattern) (guard : d64426 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64425 p = 1 := by simpa only [d64426, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2674 p hg
    simpa only [d64426, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64426, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64426, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2676 (p : Pattern) (guard : d64427 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64426 p = 1 := by simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2675 p hg
    simpa only [d64427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2677 (p : Pattern) (guard : d64428 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64427 p = 1 := by simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2676 p hg
    simpa only [d64428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2678 (p : Pattern) (guard : d64429 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64428 p = 1 := by simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2677 p hg
    simpa only [d64429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2679 (p : Pattern) (guard : d64430 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64429 p = 1 := by simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2678 p hg
    simpa only [d64430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2680 (p : Pattern) (guard : d64431 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64430 p = 1 := by simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2679 p hg
    simpa only [d64431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2681 (p : Pattern) (guard : d64432 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d64423 p = 1 := by simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64431 p = 1 := by simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2680 p hg
    simpa only [d64432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2682 (p : Pattern) (guard : d475 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2683 (p : Pattern) (guard : d476 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2623 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2682 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2684 (p : Pattern) (guard : d477 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d476 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2683 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2685 (p : Pattern) (guard : d478 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d477 p = 1 := by simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2684 p hg
    simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2686 (p : Pattern) (guard : d479 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d478 p = 1 := by simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2687 (p : Pattern) (guard : d480 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2682 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2688 (p : Pattern) (guard : d481 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2689 (p : Pattern) (guard : d482 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2688 p hg
    simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2690 (p : Pattern) (guard : d483 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2689 p hg
    simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2691 (p : Pattern) (guard : d484 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2686 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2692 (p : Pattern) (guard : d485 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d484 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2693 (p : Pattern) (guard : d511 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d485 p = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2692 p hg
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2694 (p : Pattern) (guard : d512 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d511 p = 1 := by simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2695 (p : Pattern) (guard : d488 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2696 (p : Pattern) (guard : d489 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2695 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2697 (p : Pattern) (guard : d513 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d489 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2696 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2698 (p : Pattern) (guard : d514 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d513 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2697 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2699 (p : Pattern) (guard : d515 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d512 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2694 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d514 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2698 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2700 (p : Pattern) (guard : d516 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d515 p = 1 := by simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2699 p hg
    simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2701 (p : Pattern) (guard : d517 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d516 p = 1 := by simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2700 p hg
    simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2702 (p : Pattern) (guard : d518 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d517 p = 1 := by simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2701 p hg
    simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2703 (p : Pattern) (guard : d519 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d484 p = 1 := by simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2704 (p : Pattern) (guard : d520 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d519 p = 1 := by simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2703 p hg
    simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2705 (p : Pattern) (guard : d521 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d520 p = 1 := by simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2704 p hg
    simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2706 (p : Pattern) (guard : d522 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d488 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2695 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2707 (p : Pattern) (guard : d523 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d522 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2706 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2708 (p : Pattern) (guard : d524 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d523 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2707 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2709 (p : Pattern) (guard : d525 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d521 p = 1 := by simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2705 p hg
    simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d524 p = 1 := by simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2708 p hg
    simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2710 (p : Pattern) (guard : d526 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d525 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2709 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2711 (p : Pattern) (guard : d527 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d526 p = 1 := by simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2710 p hg
    simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2712 (p : Pattern) (guard : d543 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare262 p hg
    simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2713 (p : Pattern) (guard : d544 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2712 p hg
    simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2714 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2713 p hg
    simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2715 (p : Pattern) (guard : d546 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2714 p hg
    simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2716 (p : Pattern) (guard : d547 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2715 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2717 (p : Pattern) (guard : d548 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d323 p = 1 := by simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2618 p hg
    simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2718 (p : Pattern) (guard : d549 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d548 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2717 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2719 (p : Pattern) (guard : d550 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d550, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d550, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d549 p = 1 := by simpa only [d550, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d550, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2720 (p : Pattern) (guard : d551 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d551, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d551, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d550 p = 1 := by simpa only [d551, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d551, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2721 (p : Pattern) (guard : d552 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d551 p = 1 := by simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2720 p hg
    simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d327 p = 1 := by simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2622 p hg
    simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2722 (p : Pattern) (guard : d553 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d552 p = 1 := by simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d328 p = 1 := by simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2623 p hg
    simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2723 (p : Pattern) (guard : d554 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d553 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2722 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2724 (p : Pattern) (guard : d555 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d554 p = 1 := by simpa only [d555, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d555, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d555, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d555, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2725 (p : Pattern) (guard : d556 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d556, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d556, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d555 p = 1 := by simpa only [d556, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d556, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2726 (p : Pattern) (guard : d557 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d556 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d479 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2686 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2727 (p : Pattern) (guard : d558 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d557 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2726 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2728 (p : Pattern) (guard : d559 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d558 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2727 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2729 (p : Pattern) (guard : d560 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d559 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2728 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2730 (p : Pattern) (guard : d486 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d485 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2692 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2731 (p : Pattern) (guard : d487 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d486 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2732 (p : Pattern) (guard : d561 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d560 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2729 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d487 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2733 (p : Pattern) (guard : d4408 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d561 p = 1 := by simpa only [d4408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2732 p hg
    simpa only [d4408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2734 (p : Pattern) (guard : d603 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d487 p = 1 := by simpa only [d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2735 (p : Pattern) (guard : d604 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d603 p = 1 := by simpa only [d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2736 (p : Pattern) (guard : d4409 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4408 p = 1 := by simpa only [d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2733 p hg
    simpa only [d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d604 p = 1 := by simpa only [d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2737 (p : Pattern) (guard : d51683 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d527 p = 1 := by simpa only [d51683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2711 p hg
    simpa only [d51683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4409 p = 1 := by simpa only [d51683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2736 p hg
    simpa only [d51683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2738 (p : Pattern) (guard : d51684 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d518 p = 1 := by simpa only [d51684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2702 p hg
    simpa only [d51684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51683 p = 1 := by simpa only [d51684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2737 p hg
    simpa only [d51684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2739 (p : Pattern) (guard : d51685 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51685, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51685, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51684 p = 1 := by simpa only [d51685, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d51685, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2740 (p : Pattern) (guard : d51684 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare2741 (p : Pattern) (guard : d609 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d511 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2742 (p : Pattern) (guard : d610 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d513 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2697 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2743 (p : Pattern) (guard : d611 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d609 p = 1 := by simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2741 p hg
    simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d610 p = 1 := by simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2742 p hg
    simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2744 (p : Pattern) (guard : d612 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d611 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2743 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2745 (p : Pattern) (guard : d613 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d612 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2744 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2746 (p : Pattern) (guard : d614 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d613 p = 1 := by simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2745 p hg
    simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2747 (p : Pattern) (guard : d615 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d520 p = 1 := by simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2704 p hg
    simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2748 (p : Pattern) (guard : d616 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d523 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2707 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2749 (p : Pattern) (guard : d617 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d615 p = 1 := by simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2747 p hg
    simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d616 p = 1 := by simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2748 p hg
    simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
